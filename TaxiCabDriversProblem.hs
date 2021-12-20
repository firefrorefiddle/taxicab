{-# LANGUAGE BangPatterns #-}

import qualified Data.IntMap as IM
import Data.IntMap (IntMap, (!))
import Data.List hiding (insert)
import Data.Maybe (fromJust)
import qualified Data.IntSet as S
import Control.Applicative
import Control.Arrow (second)
import Control.Monad (replicateM)
import qualified Data.ByteString.Char8 as B
import System.IO

type Coord = Int
type Distance = Int
type Coords = (Coord, Coord)
type Id = Int

type PosTree = Tree2d

answer :: Int -> Int -> Int -> [Coords] -> [(Id, Id)] -> Int
answer n h v js ps = toResult $
                     go
                     S.empty
                     1
                     (junctions ! 1)
                     (Empty :: PosTree)
  where go seen i pos prev =

          let neighbours :: [Id]
              neighbours = filter (not . flip S.member seen) $
                           IM.findWithDefault [] i conns

              seen'      = S.insert i seen

              prev'      = insert2d pos 1 prev

              (x0,y0)    = junctions ! i
              (xp,yp)    = pos              
              
              reachable :: Int
              reachable = findAtleast2d (offset pos (-h, -v)) prev
                            
              (retS, retN, retP, retF) = goChildren pos (x0,y0) prev' (seen', 0, [], []) neighbours
                   
          in (retS, retN + reachable, pos:retP, pos:retF)

        goChildren pos _       _    (seen, acc, subPrevs, retF) [] =
          (seen, acc, retF, retF)
        
        goChildren pos (x0,y0) prev (seen, acc, subPrevs, retF) (c:children) =
          let prev' = foldr (\(spx,spy) p ->
                              let (spx', spy') = offset pos (xp-spx,yp-spy)
                              in if xp - h <= spx' && yp - v <= spy'
                                 then insert2d (spx', spy') 1 p
                                 else p) prev subPrevs
              (xp,yp) = pos
              (xn,yn) = junctions ! c
              (xoff,yoff) = (abs (xn-x0),abs(yn-y0))
              (seen',acc',subPrevs',retF') = go seen c (offset pos (xoff,yoff)) prev'
          in goChildren pos (x0,y0) prev' (seen',acc+acc',retF',retF++retF') children

        offset (x0,y0) (x1,y1) = (x0+x1, y0+y1)
           
        buildNeighbourMap :: [(Id, Id)] -> IntMap [Id]
        buildNeighbourMap = foldl' (\m (x,y) ->
                                     IM.insertWith (++) y [x] $
                                     IM.insertWith (++) x [y] m)
                            IM.empty
                            
        toResult (_, reachable, _, _) = n * (n-1) `div` 2 - reachable

        junctions = IM.fromList $ zip [1..] js
        conns = buildNeighbourMap ps


parseInput :: Handle -> IO (Int, Int, Int, [Coords], [(Id, Id)])
parseInput hdl = do
  [n, h, v] <- map (fst . fromJust . B.readInt) . B.words <$> B.hGetLine hdl
  js <- replicateM (fromIntegral n) $ do
    [x, y] <- map (fst . fromJust . B.readInt) . B.words <$> B.hGetLine hdl
    return (x,y)
  ps <- replicateM (fromIntegral n - 1) $ do
    [x, y] <- map (fst . fromJust . B.readInt) . B.words <$> B.hGetLine hdl
    return (x,y)
  return (n, h, v, js, ps)

main = do
  (n, h, v, js, ps) <- parseInput stdin
  print $ answer n h v js ps

--- 3-4-5 range trees
data Tree v = Empty
            | Leaf1 {-# UNPACK #-} !Int v
            | Leaf2 v {-# UNPACK #-} !Int v {-# UNPACK #-} !Int v
            | Leaf3 v {-# UNPACK #-} !Int v {-# UNPACK #-} !Int v {-# UNPACK #-} !Int v
            | Leaf4 v {-# UNPACK #-} !Int v {-# UNPACK #-} !Int v {-# UNPACK #-} !Int v {-# UNPACK #-} !Int v
            | Leaf5 v {-# UNPACK #-} !Int v {-# UNPACK #-} !Int v {-# UNPACK #-} !Int v {-# UNPACK #-} !Int v {-# UNPACK #-} !Int v
            | Leaf6 v {-# UNPACK #-} !Int v {-# UNPACK #-} !Int v {-# UNPACK #-} !Int v {-# UNPACK #-} !Int v {-# UNPACK #-} !Int v {-# UNPACK #-} !Int v
            | Leaf7 v {-# UNPACK #-} !Int v {-# UNPACK #-} !Int v {-# UNPACK #-} !Int v {-# UNPACK #-} !Int v {-# UNPACK #-} !Int v {-# UNPACK #-} !Int v {-# UNPACK #-} !Int v
            | Tree2 v (Tree v) {-# UNPACK #-} !Int (Tree v)
            | Tree3 v (Tree v) {-# UNPACK #-} !Int (Tree v) {-# UNPACK #-} !Int (Tree v)
            | Tree4 v (Tree v) {-# UNPACK #-} !Int (Tree v) {-# UNPACK #-} !Int (Tree v) {-# UNPACK #-} !Int (Tree v)
            | Tree5 v (Tree v) {-# UNPACK #-} !Int (Tree v) {-# UNPACK #-} !Int (Tree v) {-# UNPACK #-} !Int (Tree v) {-# UNPACK #-} !Int (Tree v)
            | Tree6 v (Tree v) {-# UNPACK #-} !Int (Tree v) {-# UNPACK #-} !Int (Tree v) {-# UNPACK #-} !Int (Tree v) {-# UNPACK #-} !Int (Tree v) {-# UNPACK #-} !Int (Tree v)
            | Tree7 v (Tree v) {-# UNPACK #-} !Int (Tree v) {-# UNPACK #-} !Int (Tree v) {-# UNPACK #-} !Int (Tree v) {-# UNPACK #-} !Int (Tree v) {-# UNPACK #-} !Int (Tree v)  {-# UNPACK #-} !Int (Tree v)
            deriving (Read, Show, Eq)

type Tree2d = Tree (Tree Int)

merge combine t1 t2 =
  case (t1, t2) of
   ((Leaf1 k v), t)                 -> ins k v t
   (t, (Leaf1 k v))                 -> ins k v t
   ((Leaf2 _ k1 v1 k2 v2), t)       -> ins k1 v1 . ins k2 v2 $ t
   (t, (Leaf2 _ k1 v1 k2 v2))       -> ins k1 v1 . ins k2 v2 $ t  
   ((Leaf3 _ k1 v1 k2 v2 k3 v3), t) -> ins k1 v1 . ins k2 v2 . ins k3 v3 $ t
   (t, (Leaf3 _ k1 v1 k2 v2 k3 v3)) -> ins k1 v1 . ins k2 v2 . ins k3 v3 $ t  
   ((Leaf4 _ k1 v1 k2 v2 k3 v3 k4 v4), t) ->
                        ins k1 v1 . ins k2 v2 . ins k3 v3 . ins k4 v4 $ t
   (t, (Leaf4 _ k1 v1 k2 v2 k3 v3 k4 v4)) ->
                        ins k1 v1 . ins k2 v2 . ins k3 v3 . ins k4 v4 $ t  
   ((Leaf5 _ k1 v1 k2 v2 k3 v3 k4 v4 k5 v5), t) ->
            ins k1 v1 . ins k2 v2 . ins k3 v3 . ins k4 v4 . ins k5 v5 $ t
   (t, (Leaf5 _ k1 v1 k2 v2 k3 v3 k4 v4 k5 v5)) ->
            ins k1 v1 . ins k2 v2 . ins k3 v3 . ins k4 v4 . ins k5 v5 $ t  
   ((Leaf6 _ k1 v1 k2 v2 k3 v3 k4 v4 k5 v5 k6 v6), t) ->
     ins k1 v1 . ins k2 v2 . ins k3 v3 . ins k4 v4 . ins k5 v5 . ins k6 v6 $ t
   (t, (Leaf6 _ k1 v1 k2 v2 k3 v3 k4 v4 k5 v5 k6 v6)) ->
     ins k1 v1 . ins k2 v2 . ins k3 v3 . ins k4 v4 . ins k5 v5 . ins k6 v6 $ t
   ((Leaf7 _ k1 v1 k2 v2 k3 v3 k4 v4 k5 v5 k6 v6 k7 v7), t) ->
     ins k1 v1 . ins k2 v2 . ins k3 v3 . ins k4 v4 . ins k5 v5 . ins k6 v6 . ins k7 v7 $ t
   (t, (Leaf7 _ k1 v1 k2 v2 k3 v3 k4 v4 k5 v5 k6 v6 k7 v7)) ->
     ins k1 v1 . ins k2 v2 . ins k3 v3 . ins k4 v4 . ins k5 v5 . ins k6 v6 . ins k7 v7 $ t
   (t1, t2) -> foldr (uncurry ins) t1 (inorder t2)
  where ins = insert combine
        
insert2d :: (Int, Int) -> Int -> Tree2d -> Tree2d
insert2d (x,y) v t = insert (merge (+)) x (Leaf1 y v) t

insert :: (v -> v -> v) -> Int -> v -> Tree v -> Tree v
insert combine k v t = case insert' combine k v t of
  Right t' -> t'
  Left (tl, k, tr) -> Tree2 (value tl `combine` value tr) tl k tr

insert' :: (v -> v -> v) -> Int -> v -> Tree v -> Either (Tree v, Int, Tree v) (Tree v)

insert' _ (!k) (!v) Empty = Right $ Leaf1 k v

insert' combine (!k) (!v) l@(Leaf1 k' v')
  | k < k'    = Right $ Leaf2 v'' k v k' v'
  | otherwise = Right $ Leaf2 v'' k' v' k v
  where v'' = v' `combine` v

insert' combine (!k) (!v) l@(Leaf2 v' k1 v1 k2 v2)
  | k < k1    = Right $ Leaf3 v'' k v k1 v1 k2 v2
  | k < k2    = Right $ Leaf3 v'' k1 v1 k v k2 v2                
  | otherwise = Right $ Leaf3 v'' k1 v1 k2 v2 k v
  where v'' = v' `combine` v
        
insert' combine (!k) (!v) l@(Leaf3 v' k1 v1 k2 v2 k3 v3)
  | k < k1    = Right $ Leaf4 v'' k v k1 v1 k2 v2 k3 v3
  | k < k2    = Right $ Leaf4 v'' k1 v1 k v k2 v2 k3 v3
  | k < k3    = Right $ Leaf4 v'' k1 v1 k2 v2 k v k3 v3
  | otherwise = Right $ Leaf4 v'' k1 v1 k2 v2 k3 v3 k v
  where v'' = v' `combine` v

insert' combine (!k) (!v) l@(Leaf4 v' k1 v1 k2 v2 k3 v3 k4 v4)
  | k < k1    = Right $ Leaf5 v'' k v k1 v1 k2 v2 k3 v3 k4 v4
  | k < k2    = Right $ Leaf5 v'' k1 v1 k v k2 v2 k3 v3 k4 v4
  | k < k3    = Right $ Leaf5 v'' k1 v1 k2 v2 k v k3 v3 k4 v4
  | k < k4    = Right $ Leaf5 v'' k1 v1 k2 v2 k3 v3 k v k4 v4
  | otherwise = Right $ Leaf5 v'' k1 v1 k2 v2 k3 v3 k4 v4 k v
  where v'' = v' `combine` v        

insert' combine (!k) (!v) l@(Leaf5 v' k1 v1 k2 v2 k3 v3 k4 v4 k5 v5)
  | k < k1    = Right $ Leaf6 v'' k v k1 v1 k2 v2 k3 v3 k4 v4 k5 v5
  | k < k2    = Right $ Leaf6 v'' k1 v1 k v k2 v2 k3 v3 k4 v4 k5 v5
  | k < k3    = Right $ Leaf6 v'' k1 v1 k2 v2 k v k3 v3 k4 v4 k5 v5
  | k < k4    = Right $ Leaf6 v'' k1 v1 k2 v2 k3 v3 k v k4 v4 k5 v5
  | k < k5    = Right $ Leaf6 v'' k1 v1 k2 v2 k3 v3 k4 v4 k v k5 v5
  | otherwise = Right $ Leaf6 v'' k1 v1 k2 v2 k3 v3 k4 v4 k5 v5 k v
  where v'' = v' `combine` v        

insert' combine (!k) (!v) l@(Leaf6 v' k1 v1 k2 v2 k3 v3 k4 v4 k5 v5 k6 v6)
  | k < k1    = Right $ Leaf7 v'' k v k1 v1 k2 v2 k3 v3 k4 v4 k5 v5 k6 v6
  | k < k2    = Right $ Leaf7 v'' k1 v1 k v k2 v2 k3 v3 k4 v4 k5 v5 k6 v6
  | k < k3    = Right $ Leaf7 v'' k1 v1 k2 v2 k v k3 v3 k4 v4 k5 v5 k6 v6
  | k < k4    = Right $ Leaf7 v'' k1 v1 k2 v2 k3 v3 k v k4 v4 k5 v5 k6 v6
  | k < k5    = Right $ Leaf7 v'' k1 v1 k2 v2 k3 v3 k4 v4 k v k5 v5 k6 v6
  | k < k6    = Right $ Leaf7 v'' k1 v1 k2 v2 k3 v3 k4 v4 k5 v5 k v k6 v6
  | otherwise = Right $ Leaf7 v'' k1 v1 k2 v2 k3 v3 k4 v4 k5 v5 k6 v6 k v
  where v'' = v' `combine` v

insert' combine (!k) (!v) l@(Leaf7 _ k1 v1 k2 v2 k3 v3 k4 v4 k5 v5 k6 v6 k7 v7)
  | k < k1    = Left $ (Leaf4 vli k  v  k1 v1 k2 v2 k3 v3, k3, Leaf4 vrn k4 v4 k5 v5 k6 v6 k7 v7)
  | k < k2    = Left $ (Leaf4 vli k1 v1 k  v  k2 v2 k3 v3, k3, Leaf4 vrn k4 v4 k5 v5 k6 v6 k7 v7)
  | k < k3    = Left $ (Leaf4 vli k1 v1 k2 v2  k v  k3 v3, k3, Leaf4 vrn k4 v4 k5 v5 k6 v6 k7 v7)
  | k < k4    = Left $ (Leaf4 vli k1 v1 k2 v2 k3 v3  k v,   k, Leaf4 vrn k4 v4 k5 v5 k6 v6 k7 v7)
  | k < k5    = Left $ (Leaf4 vln k1 v1 k2 v2 k3 v3 k4 v4, k4, Leaf4 vri  k  v k5 v5 k6 v6 k7 v7)
  | k < k6    = Left $ (Leaf4 vln k1 v1 k2 v2 k3 v3 k4 v4, k4, Leaf4 vri k5 v5  k  v k6 v6 k7 v7)
  | k < k7    = Left $ (Leaf4 vln k1 v1 k2 v2 k3 v3 k4 v4, k4, Leaf4 vri k5 v5  k6 v6 k  v k7 v7)
  | otherwise = Left $ (Leaf4 vln k1 v1 k2 v2 k3 v3 k4 v4, k4, Leaf4 vri k5 v5  k6 v6 k7 v7 k  v)
  where vln = v1 `combine` v2 `combine` v3 `combine` v4
        vli = v1 `combine` v2 `combine` v3 `combine`  v
        vrn = v4 `combine` v5 `combine` v6 `combine` v7
        vri =  v `combine` v5 `combine` v6 `combine` v7
        
insert' combine (!k) (!v) (Tree2 v' l k' r)
  | k < k' = case insert' combine k v l of
              Right l'           -> Right $ Tree2 v'' l' k' r
              Left (ll, k'', lr) -> Right $ Tree3 v'' ll k'' lr k' r
  | otherwise = case insert' combine k v r of
                 Right r'           -> Right $ Tree2 v'' l k' r'
                 Left (rl, k'', rr) -> Right $ Tree3 v'' l k' rl k'' rr
  where v'' = v' `combine` v
        
insert' combine (!k) (!v) (Tree3 v' t1 k1 t2 k2 t3)
  | k < k1 = case insert' combine k v t1 of
              Right t1'            -> Right $ Tree3 v'' t1' k1 t2 k2 t3
              Left (t1l, k1', t1r) -> Right $ Tree4 v'' t1l k1' t1r k1 t2 k2 t3 
  | k < k2 = case insert' combine k v t2 of
              Right t2'            -> Right $ Tree3 v'' t1 k1 t2' k2 t3
              Left (t2l, k2', t2r) -> Right $ Tree4 v'' t1 k1 t2l k2' t2r k2 t3 
  | otherwise = case insert' combine k v t3 of
              Right t3'            -> Right $ Tree3 v'' t1 k1 t2 k2 t3'
              Left (t3l, k3', t3r) -> Right $ Tree4 v'' t1 k1 t2 k2 t3l k3' t3r
  where v'' = v' `combine` v

insert' combine (!k) (!v) (Tree4 v' t1 k1 t2 k2 t3 k3 t4)
  | k < k1 = case insert' combine k v t1 of
              Right t1'            -> Right $ Tree4 v'' t1' k1 t2 k2 t3 k3 t4
              Left (t1l, k1', t1r) -> Right $ Tree5 v'' t1l k1' t1r k1 t2 k2 t3 k3 t4
  | k < k2 = case insert' combine k v t2 of
              Right t2'            -> Right $ Tree4 v'' t1 k1 t2' k2 t3 k3 t4
              Left (t2l, k2', t2r) -> Right $ Tree5 v'' t1 k1 t2l k2' t2r k2 t3 k3 t4
  | k < k3 = case insert' combine k v t3 of
              Right t3'            -> Right $ Tree4 v'' t1 k1 t2 k2 t3' k3 t4
              Left (t3l, k3', t3r) -> Right $ Tree5 v'' t1 k1 t2 k2 t3l k3' t3r k3 t4
  | otherwise = case insert' combine k v t4 of
              Right t4'            -> Right $ Tree4 v'' t1 k1 t2 k2 t3 k3 t4'
              Left (t4l, k4', t4r) -> Right $ Tree5 v'' t1 k1 t2 k2 t3 k3 t4l k4' t4r
  where v'' = v' `combine` v        

insert' combine (!k) (!v) (Tree5 v' t1 k1 t2 k2 t3 k3 t4 k4 t5)
  | k < k1 = case insert' combine k v t1 of
              Right t1'            -> Right $ Tree5 v'' t1' k1 t2 k2 t3 k3 t4 k4 t5
              Left (t1l, k1', t1r) -> Right $ Tree6 v'' t1l k1' t1r k1 t2 k2 t3 k3 t4 k4 t5
  | k < k2 = case insert' combine k v t2 of
              Right t2'            -> Right $ Tree5 v'' t1 k1 t2' k2 t3 k3 t4 k4 t5
              Left (t2l, k2', t2r) -> Right $ Tree6 v'' t1 k1 t2l k2' t2r k2 t3 k3 t4 k4 t5
  | k < k3 = case insert' combine k v t3 of
              Right t3'            -> Right $ Tree5 v'' t1 k1 t2 k2 t3' k3 t4 k4 t5
              Left (t3l, k3', t3r) -> Right $ Tree6 v'' t1 k1 t2 k2 t3l k3' t3r k3 t4 k4 t5
  | k < k4 = case insert' combine k v t4 of
              Right t4'            -> Right $ Tree5 v'' t1 k1 t2 k2 t3 k3 t4' k4 t5
              Left (t4l, k4', t4r) -> Right $ Tree6 v'' t1 k1 t2 k2 t3 k3 t4l k4' t4r k4 t5
  | otherwise = case insert' combine k v t5 of
              Right t5'            -> Right $ Tree5 v'' t1 k1 t2 k2 t3 k3 t4 k4 t5'
              Left (t5l, k5', t5r) -> Right $ Tree6 v'' t1 k1 t2 k2 t3 k3 t4 k4 t5l k5' t5r
  where v'' = v' `combine` v        

insert' combine (!k) (!v) (Tree6 v' t1 k1 t2 k2 t3 k3 t4 k4 t5 k5 t6)
  | k < k1 = case insert' combine k v t1 of
              Right t1'            -> Right $ Tree6 v'' t1' k1 t2 k2 t3 k3 t4 k4 t5 k5 t6
              Left (t1l, k1', t1r) -> Right $ Tree7 v'' t1l k1' t1r k1 t2 k2 t3 k3 t4 k4 t5 k5 t6
  | k < k2 = case insert' combine k v t2 of
              Right t2'            -> Right $ Tree6 v'' t1 k1 t2' k2 t3 k3 t4 k4 t5 k5 t6
              Left (t2l, k2', t2r) -> Right $ Tree7 v'' t1 k1 t2l k2' t2r k2 t3 k3 t4 k4 t5 k5 t6
  | k < k3 = case insert' combine k v t3 of
              Right t3'            -> Right $ Tree6 v'' t1 k1 t2 k2 t3' k3 t4 k4 t5 k5 t6
              Left (t3l, k3', t3r) -> Right $ Tree7 v'' t1 k1 t2 k2 t3l k3' t3r k3 t4 k4 t5 k5 t6
  | k < k4 = case insert' combine k v t4 of
              Right t4'            -> Right $ Tree6 v'' t1 k1 t2 k2 t3 k3 t4' k4 t5 k5 t6
              Left (t4l, k4', t4r) -> Right $ Tree7 v'' t1 k1 t2 k2 t3 k3 t4l k4' t4r k4 t5 k5 t6
  | k < k5 = case insert' combine k v t5 of
              Right t5'            -> Right $ Tree6 v'' t1 k1 t2 k2 t3 k3 t4 k4 t5' k5 t6
              Left (t5l, k5', t5r) -> Right $ Tree7 v'' t1 k1 t2 k2 t3 k3 t4 k4 t5l k5' t5r k5 t6
  | otherwise = case insert' combine k v t6 of
              Right t6'            -> Right $ Tree6 v'' t1 k1 t2 k2 t3 k3 t4 k4 t5 k5 t6'
              Left (t6l, k6', t6r) -> Right $ Tree7 v'' t1 k1 t2 k2 t3 k3 t4 k4 t5 k5 t6l k6' t6r
  where v'' = v' `combine` v        

insert' combine (!k) (!v) (Tree7 v' t1 k1 t2 k2 t3 k3 t4 k4 t5 k5 t6 k6 t7)
  | k < k1 = case insert' combine k v t1 of
              Right t1'            -> Right $ Tree7 v'' t1' k1 t2 k2 t3 k3 t4 k4 t5 k5 t6 k6 t7
              Left (t1l, k1', t1r) -> Left  $ (Tree3 (mkval1 v [t1,t2]) t1l k1' t1r k1 t2,
                                               k2,
                                               Tree5 (mkval [t3,t4,t5,t6,t7]) t3 k3 t4 k4 t5 k5 t6 k6 t7)
  | k < k2 = case insert' combine k v t2 of
              Right t2'            -> Right $ Tree7 v'' t1 k1 t2' k2 t3 k3 t4 k4 t5 k5 t6 k6 t7
              Left (t2l, k2', t2r) -> Left  $ (Tree4 (mkval1 v [t1,t2,t3]) t1 k1 t2l k2' t2r k2 t3,
                                               k3,
                                               Tree4 (mkval [t4,t5,t6,t7]) t4 k4 t5 k5 t6 k6 t7)
  | k < k3 = case insert' combine k v t3 of
              Right t3'            -> Right $ Tree7 v'' t1 k1 t2 k2 t3' k3 t4 k4 t5 k5 t6 k6 t7
              Left (t3l, k3', t3r) -> Left  $ (Tree4 (mkval1 v [t1,t2,t3]) t1 k1 t2 k2 t3l k3' t3r,
                                               k3,
                                               Tree4 (mkval [t4,t5,t6,t7]) t4 k4 t5 k5 t6 k6 t7)
  | k < k4 = case insert' combine k v t4 of
              Right t4'            -> Right $ Tree7 v'' t1 k1 t2 k2 t3 k3 t4' k4 t5 k5 t6 k6 t7
              Left (t4l, k4', t4r) -> Left  $ (Tree4 (mkval [t1,t2,t3,t4l]) t1 k1 t2 k2 t3 k3 t4l,
                                               k4',
                                               Tree4 (mkval [t4r,t5,t6,t7]) t4r k4 t5 k5 t6 k6 t7)
  | k < k5 = case insert' combine k v t5 of
              Right t5'            -> Right $ Tree7 v'' t1 k1 t2 k2 t3 k3 t4 k4 t5' k5 t6 k6 t7
              Left (t5l, k5', t5r) -> Left  $ (Tree4 (mkval [t1,t2,t3,t4]) t1 k1 t2 k2 t3 k3 t4,
                                               k4,
                                               Tree4 (mkval1 v [t5,t6,t7]) t5l k5' t5r k5 t6 k6 t7)
  | k < k6 = case insert' combine k v t6 of
              Right t6'            -> Right $ Tree7 v'' t1 k1 t2 k2 t3 k3 t4 k4 t5 k5 t6' k6 t7
              Left (t6l, k6', t6r) -> Left  $ (Tree4 (mkval [t1,t2,t3,t4]) t1 k1 t2 k2 t3 k3 t4,
                                               k4,
                                               Tree4 (mkval1 v [t5,t6,t7]) t5 k5 t6l k6' t6r k6 t7)
  | otherwise = case insert' combine k v t7 of
              Right t7'            -> Right $ Tree7 v'' t1 k1 t2 k2 t3 k3 t4 k4 t5 k5 t6 k6 t7'
              Left (t7l, k7', t7r) -> Left  $ (Tree5 (mkval [t1,t2,t3,t4,t5]) t1 k1 t2 k2 t3 k3 t4 k4 t5,
                                               k5,
                                               Tree3 (mkval1 v [t6,t7]) t6 k6 t7l k7' t7r)
  where mkval = foldr1 combine . map value
        mkval1 v = foldr combine v . map value
        v'' = v' `combine` v

value Empty = error "empty value"
value (Leaf1 _ v) = v
value (Leaf2 v _ _ _ _) = v
value (Leaf3 v _ _ _ _ _ _) = v
value (Leaf4 v _ _ _ _ _ _ _ _) = v
value (Leaf5 v _ _ _ _ _ _ _ _ _ _) = v
value (Leaf6 v _ _ _ _ _ _ _ _ _ _ _ _) = v
value (Leaf7 v _ _ _ _ _ _ _ _ _ _ _ _ _ _) = v
value (Tree2 v _ _ _) = v
value (Tree3 v _ _ _ _ _) = v
value (Tree4 v _ _ _ _ _ _ _) = v
value (Tree5 v _ _ _ _ _ _ _ _ _) = v
value (Tree6 v _ _ _ _ _ _ _ _ _ _ _) = v
value (Tree7 v _ _ _ _ _ _ _ _ _ _ _ _ _) = v

inorder Empty = []
inorder (Leaf1 k v)                                         = [(k,v)]
inorder (Leaf2 _ k1 v1 k2 v2)                               = [(k1,v1),(k2,v2)]
inorder (Leaf3 _ k1 v1 k2 v2 k3 v3)                         = [(k1,v1),(k2,v2),(k3,v3)]
inorder (Leaf4 _ k1 v1 k2 v2 k3 v3 k4 v4)                   = [(k1,v1),(k2,v2),(k3,v3),(k4,v4)]
inorder (Leaf5 _ k1 v1 k2 v2 k3 v3 k4 v4 k5 v5)             = [(k1,v1),(k2,v2),(k3,v3),(k4,v4),(k5,v5)]
inorder (Leaf6 _ k1 v1 k2 v2 k3 v3 k4 v4 k5 v5 k6 v6)       = [(k1,v1),(k2,v2),(k3,v3),(k4,v4),(k5,v5),(k6,v6)]
inorder (Leaf7 _ k1 v1 k2 v2 k3 v3 k4 v4 k5 v5 k6 v6 k7 v7) = [(k1,v1),(k2,v2),(k3,v3),(k4,v4),(k5,v5),(k6,v6),(k7,v7)]
inorder (Tree2 _ t1 _ t2)                          = inorder t1 ++ inorder t2
inorder (Tree3 _ t1 _ t2 _ t3)                     = inorder t1 ++ inorder t2 ++ inorder t3
inorder (Tree4 _ t1 _ t2 _ t3 _ t4)                = inorder t1 ++ inorder t2 ++ inorder t3 ++ inorder t4
inorder (Tree5 _ t1 _ t2 _ t3 _ t4 _ t5)           = inorder t1 ++ inorder t2 ++ inorder t3 ++ inorder t4 ++ inorder t5
inorder (Tree6 _ t1 _ t2 _ t3 _ t4 _ t5 _ t6)      = inorder t1 ++ inorder t2 ++ inorder t3 ++ inorder t4 ++ inorder t5 ++ inorder t6
inorder (Tree7 _ t1 _ t2 _ t3 _ t4 _ t5 _ t6 _ t7) = inorder t1 ++ inorder t2 ++ inorder t3 ++ inorder t4 ++ inorder t5 ++ inorder t6 ++ inorder t7

inorder2d = concatMap (\(x,ys) -> map (\(y,v) -> ((x,y),v)) ys) . 
            map (second inorder) . inorder

findAtleast :: Int -> Tree v -> [v]
findAtleast (!k) Empty = []
findAtleast (!k) (Leaf1 k' v) | k <= k'   = [v]
                              | otherwise = []
findAtleast (!k) (Leaf2 v k1 v1 k2 v2)
  | k <= k1 = [v]
  | k <= k2 = [v2]
  | otherwise = []
findAtleast (!k) (Leaf3 v k1 v1 k2 v2 k3 v3)
  | k <= k1 = [v]
  | k <= k2 = [v2,v3]
  | k <= k3 =    [v3]
  | otherwise = []
findAtleast (!k) (Leaf4 v k1 v1 k2 v2 k3 v3 k4 v4)
  | k <= k1 = [v]
  | k <= k2 = [v2,v3,v4]
  | k <= k3 =    [v3,v4]
  | k <= k4 =       [v4]
  | otherwise = []
findAtleast (!k) (Leaf5 v k1 v1 k2 v2 k3 v3 k4 v4 k5 v5)
  | k <= k1 = [v]
  | k <= k2 = [v2,v3,v4,v5]
  | k <= k3 =    [v3,v4,v5]
  | k <= k4 =       [v4,v5]
  | k <= k5 =          [v5]
  | otherwise = []
findAtleast (!k) (Leaf6 v k1 v1 k2 v2 k3 v3 k4 v4 k5 v5 k6 v6)
  | k <= k1 = [v]
  | k <= k2 = [v2,v3,v4,v5,v6]
  | k <= k3 =    [v3,v4,v5,v6]
  | k <= k4 =       [v4,v5,v6]
  | k <= k5 =          [v5,v6]
  | k <= k6 =             [v6]
  | otherwise = []
findAtleast (!k) (Leaf7 v k1 v1 k2 v2 k3 v3 k4 v4 k5 v5 k6 v6 k7 v7)
  | k <= k1 = [v]
  | k <= k2 = [v2,v3,v4,v5,v6,v7]
  | k <= k3 =    [v3,v4,v5,v6,v7]
  | k <= k4 =       [v4,v5,v6,v7]
  | k <= k5 =          [v5,v6,v7]
  | k <= k6 =             [v6,v7]
  | k <= k7 =                [v7]
  | otherwise = []
                
findAtleast (!k) (Tree2 v t1 k' t2)
  | k <= k'   = value t2 : findAtleast k t1
  | otherwise = findAtleast k t2
                                               
findAtleast (!k) (Tree3 v t1 k1 t2 k2 t3)
  | k <= k1   = value t2 : value t3 : findAtleast k t1
  | k <= k2   =            value t3 : findAtleast k t2
  | otherwise =                       findAtleast k t3

findAtleast (!k) (Tree4 v t1 k1 t2 k2 t3 k3 t4)
  | k <= k1   = value t2 : value t3 : value t4 : findAtleast k t1
  | k <= k2   =            value t3 : value t4 : findAtleast k t2
  | k <= k3   =                       value t4 : findAtleast k t3
  | otherwise =                                  findAtleast k t4

findAtleast (!k) (Tree5 v t1 k1 t2 k2 t3 k3 t4 k4 t5)
  | k <= k1   = value t2 : value t3 : value t4 : value t5 : findAtleast k t1
  | k <= k2   =            value t3 : value t4 : value t5 : findAtleast k t2
  | k <= k3   =                       value t4 : value t5 : findAtleast k t3
  | k <= k4   =                                  value t5 : findAtleast k t4
  | otherwise =                                             findAtleast k t5

findAtleast (!k) (Tree6 v t1 k1 t2 k2 t3 k3 t4 k4 t5 k5 t6)
  | k <= k1   = value t2 : value t3 : value t4 : value t5 : value t6 : findAtleast k t1
  | k <= k2   =            value t3 : value t4 : value t5 : value t6 : findAtleast k t2
  | k <= k3   =                       value t4 : value t5 : value t6 : findAtleast k t3
  | k <= k4   =                                  value t5 : value t6 : findAtleast k t4
  | k <= k5   =                                             value t6 : findAtleast k t5
  | otherwise =                                                        findAtleast k t6

findAtleast (!k) (Tree7 v t1 k1 t2 k2 t3 k3 t4 k4 t5 k5 t6 k6 t7)
  | k <= k1   = value t2 : value t3 : value t4 : value t5 : value t6 : value t7 : findAtleast k t1
  | k <= k2   =            value t3 : value t4 : value t5 : value t6 : value t7 : findAtleast k t2
  | k <= k3   =                       value t4 : value t5 : value t6 : value t7 : findAtleast k t3
  | k <= k4   =                                  value t5 : value t6 : value t7 : findAtleast k t4
  | k <= k5   =                                             value t6 : value t7 : findAtleast k t5
  | k <= k6   =                                                        value t7 : findAtleast k t6
  | otherwise =                                                                   findAtleast k t7                                                                       

findAtleast2d (!x,!y) t = sum . concatMap (findAtleast y) . findAtleast x $ t

