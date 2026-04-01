||| Image-native replay executable.
|||
||| This executable consumes native `IMAGE_EVENT` blocks and either prints the
||| resulting `IMAGE_CONTEXT` snapshots or checks them against expected
||| `IMAGE_CONTEXT` blocks from stdin.
module ImageMain

import Data.Nat
import Data.List
import Data.String
import Data.SortedMap
import Decidable.Equality
import System
import System.File

import Peering.Types
import Peering.ObjectImage
import Peering.ImageMachine
import Peering.ImageInvariants
import Peering.ImageProcess
import Peering.ImageReplayCheck
import Peering.ImageRefinement

%default covering

parseNat : String -> Nat
parseNat s = case the (Maybe Integer) (parsePositive (trim s)) of
               Just n  => if n >= 0 then fromInteger n else 0
               Nothing => 0

parseNatMaybe : String -> Maybe Nat
parseNatMaybe s =
  let t = trim s in
  if t == "" then
    Nothing
  else if not (all isDigit (unpack t)) then
    Nothing
  else
    Just (foldl (\acc, d => acc * 10 + d) 0 (map charToNat (unpack t)))
  where
    isDigit : Char -> Bool
    isDigit c = c >= '0' && c <= '9'

    charToNat : Char -> Nat
    charToNat '0' = 0
    charToNat '1' = 1
    charToNat '2' = 2
    charToNat '3' = 3
    charToNat '4' = 4
    charToNat '5' = 5
    charToNat '6' = 6
    charToNat '7' = 7
    charToNat '8' = 8
    charToNat '9' = 9
    charToNat _ = 0

parseNatList : String -> List Nat
parseNatList s =
  let ws = words (trim s)
  in map parseNat ws

joinStrings : List String -> String
joinStrings [] = ""
joinStrings [x] = x
joinStrings (x :: xs) = x ++ " " ++ joinStrings xs

joinNatList : List Nat -> String
joinNatList [] = ""
joinNatList [x] = show x
joinNatList (x :: xs) = show x ++ " " ++ joinNatList xs

showBit : Bool -> String
showBit False = "0"
showBit True = "1"

splitOnChar : Char -> List Char -> (List Char, List Char)
splitOnChar sep [] = ([], [])
splitOnChar sep (c :: cs) =
  if c == sep
    then ([], cs)
    else let (lhs, rhs) = splitOnChar sep cs
         in (c :: lhs, rhs)

parseImageEntry : String -> Maybe (ObjectId, Length)
parseImageEntry raw =
  let (objChars, lenChars) = splitOnChar ':' (unpack (trim raw))
  in case lenChars of
       [] => Nothing
       _ =>
         case (parseNatMaybe (pack objChars), parseNatMaybe (pack lenChars)) of
           (Just objId, Just len) => Just (objId, len)
           _ => Nothing

parseImageEntries : List String -> Maybe (List (ObjectId, Length))
parseImageEntries [] = Just []
parseImageEntries (raw :: raws) =
  case parseImageEntry raw of
    Nothing => Nothing
    Just entry =>
      case parseImageEntries raws of
        Nothing => Nothing
        Just rest => Just (entry :: rest)

parseObjectImageMaybe : String -> Maybe ObjectImage
parseObjectImageMaybe raw =
  case parseImageEntries (words (trim raw)) of
    Nothing => Nothing
    Just entries => Just (imageFromList entries)

showObjectImage : ObjectImage -> String
showObjectImage image =
  joinStrings (map (\(objId, len) => show objId ++ ":" ++ show len) (imageToList image))

readLine : IO (Maybe String)
readLine = do
  Right l <- fGetLine stdin
    | Left _ => pure Nothing
  if l == ""
    then pure Nothing
    else pure (Just (trim l))

readBlock : IO (List String)
readBlock = do
  ml <- readLine
  case ml of
    Nothing => pure []
    Just l  =>
      if l == "---"
        then pure []
        else do
          rest <- readBlock
          pure (l :: rest)

lookupField : String -> List String -> Maybe String
lookupField pfx lines =
  let bare = trim pfx in
  case find (\l => isPrefixOf pfx l || l == bare) lines of
    Just l  =>
      if l == bare
        then Just ""
        else Just (trim (substr (cast (strLength pfx)) (cast (strLength l)) l))
    Nothing => Nothing

lookupFieldNat : String -> List String -> Nat
lookupFieldNat pfx lines =
  case lookupField pfx lines of
    Just v  => parseNat v
    Nothing => 0

lookupFieldNatList : String -> List String -> List Nat
lookupFieldNatList pfx lines =
  case lookupField pfx lines of
    Just v  => parseNatList v
    Nothing => []

lookupFields : String -> List String -> List String
lookupFields pfx lines =
  map (\l => trim (substr (cast (strLength pfx)) (cast (strLength l)) l))
      (filter (\l => isPrefixOf pfx l) lines)

parseBoolMaybe : String -> Maybe Bool
parseBoolMaybe s =
  case trim s of
    "0" => Just False
    "1" => Just True
    _   => Nothing

splitLast : List a -> Maybe (List a, a)
splitLast [] = Nothing
splitLast [x] = Just ([], x)
splitLast (x :: xs) =
  case splitLast xs of
    Nothing => Nothing
    Just (mid, last) => Just (x :: mid, last)

splitHeadLast : List a -> Maybe (a, List a, a)
splitHeadLast [] = Nothing
splitHeadLast [x] = Nothing
splitHeadLast (x :: xs) =
  case splitLast xs of
    Nothing => Nothing
    Just (mid, last) => Just (x, mid, last)

parseAll : (a -> Maybe b) -> List a -> Maybe (List b)
parseAll f [] = Just []
parseAll f (x :: xs) =
  case f x of
    Nothing => Nothing
    Just y =>
      case parseAll f xs of
        Nothing => Nothing
        Just ys => Just (y :: ys)

parsePeerImageField : String -> Maybe PeerImageInfo
parsePeerImageField field =
  case splitHeadLast (words (trim field)) of
    Nothing => Nothing
    Just (osdStr, imageWords, lesStr) =>
      case (parseNatMaybe osdStr,
            parseObjectImageMaybe (joinStrings imageWords),
            parseNatMaybe lesStr) of
        (Just peer, Just image, Just les) => Just (MkPeerImageInfo peer image les)
        _ => Nothing

parseAuthSourceField : String -> Maybe (ObjectId, ObjectAuthority)
parseAuthSourceField field =
  case parseNatList field of
    [objId, authOsd, authLen] => Just (objId, MkObjectAuthority authOsd authLen)
    _ => Nothing

parseObjRecoveryField : String -> Maybe ObjRecovery
parseObjRecoveryField field =
  case parseNatList field of
    [objId, fromLen', toLen'] => Just (MkObjRecovery objId fromLen' toLen')
    _ => Nothing

parsePeerRecoveryField : String -> Maybe (OsdId, ObjRecovery)
parsePeerRecoveryField field =
  case parseNatList field of
    [targetOsd, objId, fromLen', toLen'] =>
      Just (targetOsd, MkObjRecovery objId fromLen' toLen')
    _ => Nothing

insertPeerRecovery : OsdId -> ObjRecovery -> List PeerRecoveryPlan -> List PeerRecoveryPlan
insertPeerRecovery targetOsd recovery [] =
  [MkPeerRecoveryPlan targetOsd [recovery]]
insertPeerRecovery targetOsd recovery (plan :: plans) =
  if target plan == targetOsd
    then { recoveries $= (++ [recovery]) } plan :: plans
    else plan :: insertPeerRecovery targetOsd recovery plans

buildExpectedPeerRecoveryPlans : List (OsdId, ObjRecovery) -> List PeerRecoveryPlan
buildExpectedPeerRecoveryPlans =
  foldl (\plans, entry => insertPeerRecovery (fst entry) (snd entry) plans) []

parseImageEvent : List String -> Maybe ImageEvent
parseImageEvent [] = Nothing
parseImageEvent (header :: rest) =
  let lines = rest
  in case header of
    "IMAGE_EVENT Initialize" => do
      pgid <- parseNatMaybe =<< lookupField "pgid " lines
      whoami <- parseNatMaybe =<< lookupField "whoami " lines
      epoch <- parseNatMaybe =<< lookupField "epoch " lines
      localImage <- parseObjectImageMaybe =<< lookupField "local_image " lines
      les <- parseNatMaybe =<< lookupField "last_epoch_started " lines
      lis <- parseNatMaybe =<< lookupField "last_interval_started " lines
      lec <- parseNatMaybe =<< lookupField "last_epoch_clean " lines
      let actingOsds = lookupFieldNatList "acting " lines
      let upOsds = lookupFieldNatList "up " lines
      let poolSz = lookupFieldNat "pool_size " lines
      let poolMinSz = lookupFieldNat "pool_min_size " lines
      let priorOsds = lookupFieldNatList "prior_osds " lines
      let acting = MkActingSet actingOsds epoch
      let up = MkActingSet upOsds epoch
      let pool = MkPoolParams poolSz poolMinSz
      let info = MkPGImageInfo pgid localImage les lis lec
      pure (ImageInitialize pgid whoami epoch acting up pool info priorOsds)

    "IMAGE_EVENT AdvanceMap" =>
      let newEpoch = lookupFieldNat "new_epoch " lines
          newActingOsds = lookupFieldNatList "new_acting " lines
          newUpOsds = lookupFieldNatList "new_up " lines
          newPoolSz = lookupFieldNat "new_pool_size " lines
          newPoolMinSz = lookupFieldNat "new_pool_min_size " lines
          priorOsds = lookupFieldNatList "prior_osds " lines
          newActing = MkActingSet newActingOsds newEpoch
          newUp = MkActingSet newUpOsds newEpoch
          newPool = MkPoolParams newPoolSz newPoolMinSz
      in Just (ImageAdvanceMap newEpoch newActing newUp newPool priorOsds)

    "IMAGE_EVENT PeerImageReceived" => do
      from <- parseNatMaybe =<< lookupField "from " lines
      queryEpoch <- parseNatMaybe =<< lookupField "query_epoch " lines
      peerImage <- parseObjectImageMaybe =<< lookupField "peer_image " lines
      les <- parseNatMaybe =<< lookupField "last_epoch_started " lines
      let info = MkPeerImageInfo from peerImage les
      pure (ImagePeerRecv from info queryEpoch)

    "IMAGE_EVENT PeerQueryTimeout" => do
      peer <- parseNatMaybe =<< lookupField "peer " lines
      pure (ImagePeerTimeout peer)

    "IMAGE_EVENT UpThruUpdated" => do
      ep <- parseNatMaybe =<< lookupField "epoch " lines
      pure (ImageUpThruOk ep)

    "IMAGE_EVENT ActivateCommitted" =>
      Just ImageActivateCommitted

    "IMAGE_EVENT RecoveryComplete" => do
      peer <- parseNatMaybe =<< lookupField "peer " lines
      ep <- parseNatMaybe =<< lookupField "epoch " lines
      pure (ImageRecoveryDone peer ep)

    "IMAGE_EVENT AllReplicasRecovered" => do
      ep <- parseNatMaybe =<< lookupField "epoch " lines
      let peers = lookupFieldNatList "peers " lines
      pure (ImageAllRecovered ep peers)

    "IMAGE_EVENT ReplicaActivate" => do
      from <- parseNatMaybe =<< lookupField "from " lines
      actEpoch <- parseNatMaybe =<< lookupField "activation_epoch " lines
      peerImage <- parseObjectImageMaybe =<< lookupField "peer_image " lines
      les <- parseNatMaybe =<< lookupField "last_epoch_started " lines
      let info = MkPeerImageInfo from peerImage les
      pure (ImageReplicaActivate from info actEpoch)

    "IMAGE_EVENT ReplicaRecoveryComplete" => do
      actEpoch <- parseNatMaybe =<< lookupField "activation_epoch " lines
      recoveredImage <- parseObjectImageMaybe =<< lookupField "recovered_image " lines
      pure (ImageReplicaRecovDone recoveredImage actEpoch)

    "IMAGE_EVENT DeleteStart" =>
      Just ImageDeleteStart

    "IMAGE_EVENT DeleteComplete" =>
      Just ImageDeleteDone

    _ => Nothing

parseImageContext : List String -> Maybe ImageReplaySnapshot
parseImageContext [] = Nothing
parseImageContext (header :: fields) =
  if header /= "IMAGE_CONTEXT" then
    Nothing
  else do
    expectedPgid <- parseNatMaybe =<< lookupField "pgid " fields
    expectedWhoami <- parseNatMaybe =<< lookupField "whoami " fields
    expectedEpoch <- parseNatMaybe =<< lookupField "epoch " fields
    actingEpoch <- parseNatMaybe =<< lookupField "acting_epoch " fields
    upEpoch <- parseNatMaybe =<< lookupField "up_epoch " fields
    poolSize <- parseNatMaybe =<< lookupField "pool_size " fields
    poolMinSize <- parseNatMaybe =<< lookupField "pool_min_size " fields
    localImage <- parseObjectImageMaybe =<< lookupField "local_image " fields
    localLes <- parseNatMaybe =<< lookupField "local_last_epoch_started " fields
    localLis <- parseNatMaybe =<< lookupField "local_last_interval_started " fields
    localLec <- parseNatMaybe =<< lookupField "local_last_epoch_clean " fields
    expectedAuthImage <- parseObjectImageMaybe =<< lookupField "auth_image " fields
    lastPeeringReset <- parseNatMaybe =<< lookupField "last_peering_reset " fields
    haveEnoughInfo <- parseBoolMaybe =<< lookupField "have_enough_info " fields
    imageInvariant <- parseBoolMaybe =<< lookupField "image_invariant " fields
    imageClean <- parseBoolMaybe =<< lookupField "image_clean " fields
    imageRecovering <- parseBoolMaybe =<< lookupField "image_recovering " fields
    needUpThru <- parseBoolMaybe =<< lookupField "need_up_thru " fields
    activated <- parseBoolMaybe =<< lookupField "activated " fields
    pendingActChange <- parseBoolMaybe =<< lookupField "pending_acting_change " fields
    authSources' <- parseAll parseAuthSourceField (lookupFields "auth_source " fields)
    peerImages' <- parseAll parsePeerImageField (lookupFields "peer_image " fields)
    peerRecoveryEntries <- parseAll parsePeerRecoveryField (lookupFields "peer_recovery " fields)
    localRecoveryPlan' <- parseAll parseObjRecoveryField (lookupFields "local_recovery " fields)
    let actingOsds = lookupFieldNatList "acting " fields
    let upOsds = lookupFieldNatList "up " fields
    let peersQueried' = lookupFieldNatList "peers_queried " fields
    let peersResponded' = lookupFieldNatList "peers_responded " fields
    let priorOsds' = lookupFieldNatList "prior_osds " fields
    let recovered' = lookupFieldNatList "recovered " fields
    let timedOutProbes' = lookupFieldNatList "timed_out_probes " fields
    let acting' = MkActingSet actingOsds actingEpoch
    let up' = MkActingSet upOsds upEpoch
    let pool' = MkPoolParams poolSize poolMinSize
    let localInfo' = MkPGImageInfo expectedPgid localImage localLes localLis localLec
    let peerRecoveryPlans' = buildExpectedPeerRecoveryPlans peerRecoveryEntries
    pure (MkImageObservedSnapshot expectedPgid
                                   expectedWhoami
                                   expectedEpoch
                                   acting'
                                   up'
                                   pool'
                                   localInfo'
                                   expectedAuthImage
                                   authSources'
                                   peerImages'
                                   peersQueried'
                                   peersResponded'
                                   priorOsds'
                                   peerRecoveryPlans'
                                   localRecoveryPlan'
                                   recovered'
                                   timedOutProbes'
                                   needUpThru
                                   activated
                                   pendingActChange
                                   lastPeeringReset
                                   haveEnoughInfo
                                   imageInvariant
                                   imageClean
                                   imageRecovering)

printPeerImageLines : List PeerImageInfo -> IO ()
printPeerImageLines [] = pure ()
printPeerImageLines (p :: ps) = do
  putStrLn ("peer_image " ++ show (osd p) ++ " " ++ showObjectImage (image p) ++ " " ++ show (lastEpochStarted p))
  printPeerImageLines ps

printAuthSourceLines : List (ObjectId, ObjectAuthority) -> IO ()
printAuthSourceLines [] = pure ()
printAuthSourceLines ((objId, auth) :: rest) = do
  let authPeer = authorityOsd auth
  let authLen = authorityLength auth
  putStrLn ("auth_source " ++ show objId ++ " " ++ show authPeer ++ " " ++ show authLen)
  printAuthSourceLines rest

printObjRecoveryLines : String -> List ObjRecovery -> IO ()
printObjRecoveryLines label [] = pure ()
printObjRecoveryLines label (item :: items) = do
  putStrLn (label ++ " " ++ show (obj item) ++ " " ++ show (fromLen item) ++ " " ++ show (toLen item))
  printObjRecoveryLines label items

printPeerRecoveryPlanLines : List PeerRecoveryPlan -> IO ()
printPeerRecoveryPlanLines [] = pure ()
printPeerRecoveryPlanLines (plan :: plans) = do
  let label = "peer_recovery " ++ show (target plan)
  printObjRecoveryLines label (recoveries plan)
  printPeerRecoveryPlanLines plans

printImageContext : ImageContext -> IO ()
printImageContext ctx = do
  putStrLn "IMAGE_CONTEXT"
  putStrLn ("pgid " ++ show (pgid ctx))
  putStrLn ("whoami " ++ show (whoami ctx))
  putStrLn ("epoch " ++ show (epoch ctx))
  putStrLn ("acting " ++ joinNatList (osds (acting ctx)))
  putStrLn ("acting_epoch " ++ show (epoch (acting ctx)))
  putStrLn ("up " ++ joinNatList (osds (up ctx)))
  putStrLn ("up_epoch " ++ show (epoch (up ctx)))
  putStrLn ("pool_size " ++ show (size (pool ctx)))
  putStrLn ("pool_min_size " ++ show (minSize (pool ctx)))
  putStrLn ("local_image " ++ showObjectImage (image (localImageInfo ctx)))
  putStrLn ("local_last_epoch_started " ++ show (lastEpochStarted (localImageInfo ctx)))
  putStrLn ("local_last_interval_started " ++ show (lastIntervalStarted (localImageInfo ctx)))
  putStrLn ("local_last_epoch_clean " ++ show (lastEpochClean (localImageInfo ctx)))
  putStrLn ("auth_image " ++ showObjectImage (authImage ctx))
  printAuthSourceLines (toList (authSources ctx))
  printPeerImageLines (peerImages ctx)
  putStrLn ("peers_queried " ++ joinNatList (peersQueried ctx))
  putStrLn ("peers_responded " ++ joinNatList (peersResponded ctx))
  putStrLn ("prior_osds " ++ joinNatList (priorOsds ctx))
  printPeerRecoveryPlanLines (peerRecoveryPlans ctx)
  printObjRecoveryLines "local_recovery" (localRecoveryPlan ctx)
  putStrLn ("recovered " ++ joinNatList (recoveredPeers ctx))
  putStrLn ("timed_out_probes " ++ joinNatList (timedOutProbes ctx))
  putStrLn ("need_up_thru " ++ showBit (needUpThru ctx))
  putStrLn ("activated " ++ showBit (activated ctx))
  putStrLn ("pending_acting_change " ++ showBit (pendingActChange ctx))
  putStrLn ("last_peering_reset " ++ show (lastPeeringReset ctx))
  putStrLn ("have_enough_info " ++ showBit (haveEnoughImageInfo ctx))
  putStrLn ("image_invariant " ++ showBit (imageContextInvariant ctx))
  putStrLn ("image_clean " ++ showBit (imageContextClean ctx))
  putStrLn ("image_recovering " ++ showBit (imageContextRecovering ctx))
  putStrLn "---"

readEventBlock : IO (Maybe (List String))
readEventBlock = do
  ml <- readLine
  case ml of
    Nothing => pure Nothing
    Just l  =>
      if l == "SEQUENCE"
        then pure (Just ["SEQUENCE"])
        else do
          rest <- readBlock
          pure (Just (l :: rest))

readExpectedImageContextBlock : IO (Maybe ImageReplaySnapshot)
readExpectedImageContextBlock = do
  ml <- readLine
  case ml of
    Nothing => pure Nothing
    Just header =>
      if header /= "IMAGE_CONTEXT" then
        pure Nothing
      else do
        fields <- readBlock
        pure $ parseImageContext (header :: fields)

showImageObservedSummary : ImageReplaySnapshot -> String
showImageObservedSummary snap =
  "IMAGE_CONTEXT epoch " ++ show snap.snapEpoch ++
  " auth_image [" ++ showObjectImage snap.snapAuthImage ++ "]" ++
  " local_image [" ++ showObjectImage (image snap.snapLocalInfo) ++ "]" ++
  " peer_images " ++ show (length snap.snapPeerImages) ++
  " peer_recovery_plans " ++ show (length snap.snapPeerRecoveryPlans) ++
  " activated " ++ showBit snap.snapActivated

showObservableImageObservedSummary : ImageReplaySnapshot -> String
showObservableImageObservedSummary snap =
  let obs = snapshotObservableState snap
  in "OBS_IMAGE epoch " ++ show obs.obsEpoch ++
     " auth_image [" ++ showObjectImage obs.obsAuthImage ++ "]" ++
     " local_image [" ++ showObjectImage (image obs.obsLocalInfo) ++ "]" ++
     " peer_images " ++ show (length obs.obsPeerImages) ++
     " peer_recovery_plans " ++ show (length obs.obsPeerRecoveryPlans) ++
     " activated " ++ showBit obs.obsActivated

showActingSetDetailed : ActingSet -> String
showActingSetDetailed acting =
  "[" ++ joinNatList (osds acting) ++ "]@" ++ show (epoch acting)

showPoolDetailed : PoolParams -> String
showPoolDetailed pool =
  "{size=" ++ show (size pool) ++ ", min=" ++ show (minSize pool) ++ "}"

fieldDiff : Bool -> String -> String -> String -> List String
fieldDiff same label expected actual =
  if same
     then []
     else ["  " ++ label ++ ": expected " ++ expected ++ ", actual " ++ actual]

showImageObservedDiffs : ImageReplaySnapshot -> ImageReplaySnapshot -> List String
showImageObservedDiffs expected actual =
  fieldDiff (expected.snapPgid == actual.snapPgid)
            "pgid"
            (show expected.snapPgid)
            (show actual.snapPgid)
  ++ fieldDiff (expected.snapWhoami == actual.snapWhoami)
               "whoami"
               (show expected.snapWhoami)
               (show actual.snapWhoami)
  ++ fieldDiff (expected.snapEpoch == actual.snapEpoch)
               "epoch"
               (show expected.snapEpoch)
               (show actual.snapEpoch)
  ++ fieldDiff (expected.snapActing == actual.snapActing)
               "acting"
               (showActingSetDetailed expected.snapActing)
               (showActingSetDetailed actual.snapActing)
  ++ fieldDiff (expected.snapUp == actual.snapUp)
               "up"
               (showActingSetDetailed expected.snapUp)
               (showActingSetDetailed actual.snapUp)
  ++ fieldDiff (expected.snapPool == actual.snapPool)
               "pool"
               (showPoolDetailed expected.snapPool)
               (showPoolDetailed actual.snapPool)
  ++ fieldDiff (expected.snapLocalInfo == actual.snapLocalInfo)
               "local_info"
               (show expected.snapLocalInfo)
               (show actual.snapLocalInfo)
  ++ fieldDiff (expected.snapAuthImage == actual.snapAuthImage)
               "auth_image"
               (showObjectImage expected.snapAuthImage)
               (showObjectImage actual.snapAuthImage)
  ++ fieldDiff (expected.snapAuthSources == actual.snapAuthSources)
               "auth_sources"
               (show expected.snapAuthSources)
               (show actual.snapAuthSources)
  ++ fieldDiff (expected.snapPeerImages == actual.snapPeerImages)
               "peer_images"
               (show expected.snapPeerImages)
               (show actual.snapPeerImages)
  ++ fieldDiff (expected.snapPeersQueried == actual.snapPeersQueried)
               "peers_queried"
               (show expected.snapPeersQueried)
               (show actual.snapPeersQueried)
  ++ fieldDiff (expected.snapPeersResponded == actual.snapPeersResponded)
               "peers_responded"
               (show expected.snapPeersResponded)
               (show actual.snapPeersResponded)
  ++ fieldDiff (expected.snapPriorOsds == actual.snapPriorOsds)
               "prior_osds"
               (show expected.snapPriorOsds)
               (show actual.snapPriorOsds)
  ++ fieldDiff (expected.snapPeerRecoveryPlans == actual.snapPeerRecoveryPlans)
               "peer_recovery_plans"
               (show expected.snapPeerRecoveryPlans)
               (show actual.snapPeerRecoveryPlans)
  ++ fieldDiff (expected.snapLocalRecoveryPlan == actual.snapLocalRecoveryPlan)
               "local_recovery_plan"
               (show expected.snapLocalRecoveryPlan)
               (show actual.snapLocalRecoveryPlan)
  ++ fieldDiff (expected.snapRecovered == actual.snapRecovered)
               "recovered"
               (show expected.snapRecovered)
               (show actual.snapRecovered)
  ++ fieldDiff (expected.snapTimedOutProbes == actual.snapTimedOutProbes)
               "timed_out_probes"
               (show expected.snapTimedOutProbes)
               (show actual.snapTimedOutProbes)
  ++ fieldDiff (expected.snapNeedUpThru == actual.snapNeedUpThru)
               "need_up_thru"
               (showBit expected.snapNeedUpThru)
               (showBit actual.snapNeedUpThru)
  ++ fieldDiff (expected.snapActivated == actual.snapActivated)
               "activated"
               (showBit expected.snapActivated)
               (showBit actual.snapActivated)
  ++ fieldDiff (expected.snapPendingActChange == actual.snapPendingActChange)
               "pending_acting_change"
               (showBit expected.snapPendingActChange)
               (showBit actual.snapPendingActChange)
  ++ fieldDiff (expected.snapLastPeeringReset == actual.snapLastPeeringReset)
               "last_peering_reset"
               (show expected.snapLastPeeringReset)
               (show actual.snapLastPeeringReset)
  ++ fieldDiff (expected.snapHaveEnoughInfo == actual.snapHaveEnoughInfo)
               "have_enough_info"
               (showBit expected.snapHaveEnoughInfo)
               (showBit actual.snapHaveEnoughInfo)
  ++ fieldDiff (expected.snapImageInvariant == actual.snapImageInvariant)
               "image_invariant"
               (showBit expected.snapImageInvariant)
               (showBit actual.snapImageInvariant)
  ++ fieldDiff (expected.snapImageClean == actual.snapImageClean)
               "image_clean"
               (showBit expected.snapImageClean)
               (showBit actual.snapImageClean)
  ++ fieldDiff (expected.snapImageRecovering == actual.snapImageRecovering)
               "image_recovering"
               (showBit expected.snapImageRecovering)
               (showBit actual.snapImageRecovering)

showObservableImageObservedDiffs : ImageReplaySnapshot -> ImageReplaySnapshot -> List String
showObservableImageObservedDiffs expected actual =
  let expectedObs = observableSnapshotOfObserved expected
      actualObs = observableSnapshotOfObserved actual in
  fieldDiff (expectedObs.proofPgid == actualObs.proofPgid)
            "proof_pgid"
            (show expectedObs.proofPgid)
            (show actualObs.proofPgid)
  ++ fieldDiff (expectedObs.proofWhoami == actualObs.proofWhoami)
               "proof_whoami"
               (show expectedObs.proofWhoami)
               (show actualObs.proofWhoami)
  ++ fieldDiff (expectedObs.proofEpoch == actualObs.proofEpoch)
               "proof_epoch"
               (show expectedObs.proofEpoch)
               (show actualObs.proofEpoch)
  ++ fieldDiff (expectedObs.proofActing == actualObs.proofActing)
               "proof_acting"
               (showActingSetDetailed expectedObs.proofActing)
               (showActingSetDetailed actualObs.proofActing)
  ++ fieldDiff (expectedObs.proofUp == actualObs.proofUp)
               "proof_up"
               (showActingSetDetailed expectedObs.proofUp)
               (showActingSetDetailed actualObs.proofUp)
  ++ fieldDiff (expectedObs.proofPool == actualObs.proofPool)
               "proof_pool"
               (showPoolDetailed expectedObs.proofPool)
               (showPoolDetailed actualObs.proofPool)
  ++ fieldDiff (expectedObs.proofLocalInfo == actualObs.proofLocalInfo)
               "proof_local_info"
               (show expectedObs.proofLocalInfo)
               (show actualObs.proofLocalInfo)
  ++ fieldDiff (expectedObs.proofPeerImages == actualObs.proofPeerImages)
               "proof_peer_images"
               (show expectedObs.proofPeerImages)
               (show actualObs.proofPeerImages)
  ++ fieldDiff (expectedObs.proofAuthImage == actualObs.proofAuthImage)
               "proof_auth_image"
               (showObjectImage expectedObs.proofAuthImage)
               (showObjectImage actualObs.proofAuthImage)
  ++ fieldDiff (expectedObs.proofPeerRecoveryPlans == actualObs.proofPeerRecoveryPlans)
               "proof_peer_recovery_plans"
               (show expectedObs.proofPeerRecoveryPlans)
               (show actualObs.proofPeerRecoveryPlans)
  ++ fieldDiff (expectedObs.proofLocalRecoveryPlan == actualObs.proofLocalRecoveryPlan)
               "proof_local_recovery_plan"
               (show expectedObs.proofLocalRecoveryPlan)
               (show actualObs.proofLocalRecoveryPlan)
  ++ fieldDiff (expectedObs.proofActivated == actualObs.proofActivated)
               "proof_activated"
               (showBit expectedObs.proofActivated)
               (showBit actualObs.proofActivated)

reportImageMismatch : Nat -> ImageReplaySnapshot -> ImageReplaySnapshot -> IO ()
reportImageMismatch evIdx actual expected = do
  ignore $ fPutStrLn stderr ("Image mismatch event #" ++ show evIdx ++
    "\n  expected: " ++ showImageObservedSummary expected ++
    "\n  actual  : " ++ showImageObservedSummary actual)
  traverse_ (fPutStrLn stderr) (showImageObservedDiffs expected actual)

reportObservableImageMismatch : Nat -> ImageReplaySnapshot -> ImageReplaySnapshot -> IO ()
reportObservableImageMismatch evIdx actual expected = do
  ignore $ fPutStrLn stderr ("Observable image mismatch event #" ++ show evIdx ++
    "\n  expected: " ++ showObservableImageObservedSummary expected ++
    "\n  actual  : " ++ showObservableImageObservedSummary actual)
  traverse_ (fPutStrLn stderr) (showObservableImageObservedDiffs expected actual)

record ImageReplaySequenceState where
  constructor MkImageReplaySequenceState
  seqCtx         : ImageContext
  seqEventsRev   : List ImageEvent
  seqHasFailure  : Bool
  seqStarted     : Bool
  seqEventCount  : Nat

emptyImageReplaySequenceState : ImageReplaySequenceState
emptyImageReplaySequenceState =
  MkImageReplaySequenceState emptyImageCtx [] False False 0

covering
finishImageReplaySequence
  : ImageReplaySequenceState -> Nat -> Nat -> IO (Nat, Nat)
finishImageReplaySequence seqState successCount failureCount =
  if not seqState.seqStarted
    then pure (successCount, failureCount)
    else if seqState.seqHasFailure
      then pure (successCount, failureCount + 1)
      else
        case buildNativeImageReplayEventTraceRefinement
               emptyImageCtx
               (reverse seqState.seqEventsRev) of
          Right _ =>
            pure (successCount + 1, failureCount)
          Left failure => do
            ignore $ fPutStrLn stderr
              ("Typed replay trace refinement failed at sequence end after "
                ++ show seqState.seqEventCount
                ++ " events: "
                ++ showNativeImageReplayFailure failure)
            pure (successCount, failureCount + 1)

covering
processImageLoop : ImageContext -> Nat -> IO ()
processImageLoop ctx evCount = do
  mblock <- readEventBlock
  case mblock of
    Nothing => do
      ignore $ fPutStrLn stderr ("Idris image replay complete: " ++ show evCount ++ " events")
      pure ()
    Just ["SEQUENCE"] =>
      processImageLoop emptyImageCtx evCount
    Just eventLines =>
      case parseImageEvent eventLines of
        Nothing => do
          ignore $ fPutStrLn stderr ("WARN: failed to parse image event: " ++ show eventLines)
          processImageLoop ctx evCount
        Just evt => do
          let finalCtx = (processNativeImage ctx evt).ctx
          printImageContext finalCtx
          processImageLoop finalCtx (evCount + 1)

covering
processImageCheckLoop : ImageReplaySequenceState -> Nat -> Nat -> Nat -> IO ()
processImageCheckLoop seqState evCount successCount failureCount = do
  mblock <- readEventBlock
  case mblock of
    Nothing => do
      (successCount', failureCount') <-
        finishImageReplaySequence seqState successCount failureCount
      ignore $ fPutStrLn stderr ("Idris image check complete: " ++ show evCount ++ " events, "
                        ++ show successCount' ++ " typed sequence witnesses, "
                        ++ show failureCount' ++ " sequence failures")
      pure ()
    Just ["SEQUENCE"] =>
      do
        (successCount', failureCount') <-
          finishImageReplaySequence seqState successCount failureCount
        processImageCheckLoop emptyImageReplaySequenceState
                              evCount
                              successCount'
                              failureCount'
    Just eventLines =>
      case parseImageEvent eventLines of
        Nothing => do
          ignore $ fPutStrLn stderr ("WARN: failed to parse image event: " ++ show eventLines)
          _ <- readExpectedImageContextBlock
          let nextSeqState =
                { seqHasFailure := True
                , seqStarted := True
                } seqState
          processImageCheckLoop nextSeqState evCount successCount failureCount
        Just evt => do
          let finalCtx = (processNativeImage seqState.seqCtx evt).ctx
          let actual = imageObservedSnapshot finalCtx
          printImageContext finalCtx
          mExpected <- readExpectedImageContextBlock
          case mExpected of
            Nothing => do
              ignore $ fPutStrLn stderr ("WARN: failed to parse expected image context at event #" ++ show (evCount + 1))
              let nextSeqState =
                    { seqCtx := finalCtx
                    , seqHasFailure := True
                    , seqStarted := True
                    , seqEventCount := seqState.seqEventCount + 1
                    } seqState
              processImageCheckLoop nextSeqState
                                    (evCount + 1)
                                    successCount
                                    failureCount
            Just expected =>
              case checkNativeImageReplayStep seqState.seqCtx evt expected of
                Right _ =>
                  let nextSeqState =
                        { seqCtx := finalCtx
                        , seqEventsRev := evt :: seqState.seqEventsRev
                        , seqStarted := True
                        , seqEventCount := seqState.seqEventCount + 1
                        } seqState
                  in processImageCheckLoop nextSeqState
                                           (evCount + 1)
                                           successCount
                                           failureCount
                Left failure => do
                  ignore $ fPutStrLn stderr
                    ("Typed replay check failed at event #" ++ show (evCount + 1)
                      ++ ": " ++ showNativeImageReplayFailure failure)
                  case failure of
                    CurrentInvariantUnavailable =>
                      ignore $ fPutStrLn stderr
                        ("  " ++ showImageInvariantBreakdown seqState.seqCtx)
                    NextInvariantUnavailable =>
                      ignore $ fPutStrLn stderr
                        ("  " ++ showImageInvariantBreakdown finalCtx)
                    CurrentSemanticBoundaryUnavailable => do
                      ignore $ fPutStrLn stderr
                        ("  " ++ showImageSemanticBoundaryBreakdown seqState.seqCtx)
                      ignore $ fPutStrLn stderr
                        ("  " ++ showImageObservableBoundaryBreakdown seqState.seqCtx)
                    NextSemanticBoundaryUnavailable => do
                      ignore $ fPutStrLn stderr
                        ("  " ++ showImageSemanticBoundaryBreakdown finalCtx)
                      ignore $ fPutStrLn stderr
                        ("  " ++ showImageObservableBoundaryBreakdown finalCtx)
                    CurrentObservableBoundaryUnavailable =>
                      ignore $ fPutStrLn stderr
                        ("  " ++ showImageObservableBoundaryBreakdown seqState.seqCtx)
                    NextObservableBoundaryUnavailable =>
                      ignore $ fPutStrLn stderr
                        ("  " ++ showImageObservableBoundaryBreakdown finalCtx)
                    NextObservableSnapshotUnsafe =>
                      ignore $ fPutStrLn stderr
                        ("  " ++ showImageObservableBoundaryBreakdown finalCtx)
                    ExpectedSnapshotMismatch => pure ()
                    TraceRefinementUnavailable => pure ()
                  reportImageMismatch (evCount + 1) actual expected
                  reportObservableImageMismatch (evCount + 1) actual expected
                  let nextSeqState =
                        { seqCtx := finalCtx
                        , seqHasFailure := True
                        , seqStarted := True
                        , seqEventCount := seqState.seqEventCount + 1
                        } seqState
                  processImageCheckLoop nextSeqState
                                        (evCount + 1)
                                        successCount
                                        failureCount

covering
main : IO ()
main = do
  args <- getArgs
  if elem "--image-native" args || elem "--dump" args
    then do
      ignore $ fPutStrLn stderr "Idris image-native replay"
      processImageLoop emptyImageCtx 0
    else do
      ignore $ fPutStrLn stderr "Idris image-native replay check"
      processImageCheckLoop emptyImageReplaySequenceState 0 0 0
