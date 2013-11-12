> {-# LANGUAGE TypeSynonymInstances, FlexibleInstances #-}

> module CVICompile where

> import Control.Monad
> import Control.Applicative
> import Data.Traversable
> import Data.Foldable
> import Data.List hiding (any)
> import Prelude hiding (any)

> import Debug.Trace

> import CVIParse
> import LLL

> data WVar = WF WFlex | WR WRigid deriving (Show, Eq)
> data WFlex = WFName String | WFWire Int (Extent Int) deriving (Show, Eq)
> data WRigid = WRIn Int | WROut COut | WRV Bit deriving (Show, Eq)
> data COut = COut Int (Extent Int) deriving (Show, Eq)
> data PVar = PF WFlex | PC COut | PG String deriving (Show, Eq)
> data TV = TF PVar | TR String deriving (Show, Eq)

> type Glob = (Val, [Type String], [(Int, Type String)])

> data TCStuf = TCStuf -- must be kept normalized
>   {  prog   :: Prog COut PVar
>   ,  wflex  :: [(WFlex, WVar)]
>   ,  tyds   :: [(PVar, Type TV)]
>   ,  globs  :: [(String, Glob)]
>   }  deriving Show

> noStuf :: TCStuf
> noStuf = TCStuf ([], []) [] [] []

> type Place = (Int, Extent Tile)

> data Barf
>   = CBarf (Place, String)
>   | LBarf (Int, String)
>   | DBarf (String, String)
>   deriving Show

> newtype TC x = TC {tc :: TCStuf -> Either Barf (x, TCStuf)}
> instance Monad TC where
>   return x = TC $ \ s -> Right (x, s)
>   ca >>= acb = TC $ \ s -> do
>     (a, s) <- tc ca s
>     tc (acb a) s
> instance Applicative TC where
>   pure = return
>   (<*>) = ap
> instance Functor TC where
>   fmap = ap . return

> barf :: Barf -> TC a
> barf b = TC $ \ _ -> Left b

> stuf :: TC TCStuf
> stuf = TC $ \ s -> Right (s, s)

> tyDef :: PVar -> Type TV -> TC ()
> tyDef u t = TC $ \ s ->
>   Right ((), s {tyds = (u, t) : map blat (tyds s)})
>   where blat (x, r) = (x, r >>= \ y -> if y == TF u then t else V y)

> occurs :: PVar -> Type TV -> Bool
> occurs p = any $ \ q -> q == TF p

> class Unify t where
>   normal :: t -> TC t
>   unify  :: Place -> t -> t -> TC t -- all normal

> instance Unify (Type TV) where
>   normal t = do
>     sb <- tyds <$> stuf
>     return $ t >>= \ x -> case x of
>       TR x -> V (TR x)
>       TF u -> case lookup u sb of
>         Just t -> t
>         Nothing -> V x
>   unify w (V x) (V y) | x == y = return (V x)
>   unify w (V (TR _)) (V (TR _)) =
>     barf (CBarf (w, "I couldn't match the types."))
>   unify w (V (TF x)) t
>     | occurs x t  = barf (CBarf (w, "I couldn't match the types."))
>     | otherwise   = tyDef x t >> return t
>   unify w t (V (TF x))
>     | occurs x t  = barf (CBarf (w, "I couldn't match the types."))
>     | otherwise   = tyDef x t >> return t
>   unify w B B = return B
>   unify w (T ss) (T ts) = T <$> unify w ss ts
>   unify w (ss :-> iss) (ts :-> its) = do
>     (us, ius) <- unify w (ss, iss) (ts, its)
>     return (us :-> ius)
>   unify w _ _ = barf (CBarf (w, "I couldn't match the types."))

> instance Unify Int where
>   normal = return
>   unify w i j  | i == j = return i
>                | otherwise = barf (CBarf (w, "I couldn't match the types."))

> instance (Unify s, Unify t) => Unify (s, t) where
>   normal (s, t) = (,) <$> normal s <*> normal t
>   unify w (s, t) (s', t') = do
>     s <- unify w s s'
>     t <- normal t
>     t' <- normal t'
>     t <- unify w t t'
>     (,) <$> normal s <*> pure t

> instance Unify t => Unify [t] where
>   normal = traverse normal
>   unify w [] [] = return []
>   unify w (s : ss) (t : ts) = do
>     (u, us) <- unify w (s, ss) (t, ts)
>     return (u : us)
>   unify w _ _ = barf (CBarf (w, "I couldn't match the types."))

> type Signal = (WVar, Type TV)

> flexConnect :: WFlex -> WVar -> TC ()
> flexConnect w x = TC $ \ s ->
>   let wact (a, WF b) | b == w = (a, x)
>       wact ab = ab
>       wf = (w, x) : map wact (wflex s)
>       sub (PF a) | a == w = wvar x
>       sub v = Def v
>       sdef (fs, e) = (fs, e >>= sub)
>       (ds, es) = prog s
>   in  return ((), s {wflex = wf, prog = (map sdef ds, map (>>= sub) es)})

> wvar :: WVar -> Exp PVar
> wvar (WF w) = Def (PF w)
> wvar (WR (WRIn i)) = In i
> wvar (WR (WROut c)) = Def (PC c)
> wvar (WR (WRV b)) = Con b

> instance Unify WVar where
>   normal (WR x) = return (WR x)
>   normal (WF w) = do
>     wdefs <- wflex <$> stuf
>     case lookup w wdefs of
>       Just w -> return w
>       Nothing -> return (WF w)
>   unify w i o | i == o = return o
>   unify _ (WF w) o = flexConnect w o >> return o
>   unify _ i (WF w) = flexConnect w i >> return i
>   unify w _ _ = barf (CBarf (w, "Two signals collided."))

> tcWire :: Place -> [Signal] -> Signal ->
>             Dir -> [(Int, Dir)] -> TC (Signal, [Signal], [Signal])
> tcWire w fs o Dn ids = do
>   (o, g, h) <- tcCross w fs o ids
>   return (o, o : g, h)
> tcWire w fs o Up ids = do
>   ([i], fs) <- gimme w 1 fs
>   o <- unify w i o
>   fs <- traverse normal fs
>   tcCross w fs o ids

> tcCross :: Place -> [Signal] -> Signal -> [(Int, Dir)] ->
>   TC (Signal, [Signal], [Signal])
> tcCross w fs o [] = return (o, [], fs)
> tcCross w fs o ((i, d) : ids) = do
>   (gs, fs) <- gimme w i fs
>   (o, gs', hs) <- tcWire w fs o d ids
>   gs <- normal gs
>   return (o, gs ++ gs', hs)

> below :: Int -> [Int]
> below n = [0 .. (n - 1)]

> cout :: Place -> COut
> cout (y, Extent l (s, _) r) = COut y (Extent l (s, 0) r)

> couts :: Place -> Int -> [COut]
> couts (y, Extent l (s, _) r) n =
>   [COut y (Extent l (s, i) r) | i <- below n]

> wirev :: Place -> WFlex
> wirev (y, Extent l (s, _) r) = WFWire y (Extent l (s, 0) r)

> wirevs :: Place -> Int -> [WFlex]
> wirevs (y, Extent l (s, _) r) n =
>   [WFWire y (Extent l (s, i) r) | i <- below n]

> mkT :: Place -> Int -> Type TV -> TC [Type TV]
> mkT w n (T ts) | n == length ts = return ts
> mkT w n t = do
>   T us <- unify w t (T (map (V . TF . PC) (couts w n)))
>   return us

> progLet :: [COut] -> Exp PVar -> TC ()
> progLet xs e = TC $ \ s ->
>   let (ds, es) = prog s
>   in  Right ((), s {prog = ((xs, e) : ds, es)})

> gimme :: Place -> Int -> [Signal] -> TC ([Signal], [Signal])
> gimme w 0 fs = return ([], fs)
> gimme w n [] = barf (CBarf (w, "I couldn't find enough inputs."))
> gimme w n (f : fs) = do
>   (gs, hs) <- gimme w (n - 1) fs
>   return (f : gs, hs)

> tcTile :: [Signal] -> Place -> TC ([Signal], [Signal])
> tcTile fs w@(_, Extent _ (_, t) _) = case t of
>   Wire d ids -> do
>     let me = wirev w
>     (_, g, h) <- tcWire w fs (WF me, V (TF (PF me))) d ids
>     return (g, h)
>   Var x Dn -> do
>     o <- normal (WF (WFName x), V (TF (PF (WFName x))))
>     return ([o], fs)
>   Var x Up -> do
>     ([i], fs) <- gimme w 1 fs
>     o <- normal (WF (WFName x), V (TF (PF (WFName x))))
>     _ <- unify w o i
>     (,) [] <$> normal fs
>   SplitFrom Up n -> do
>     ([(i, t)], fs) <- gimme w 1 fs
>     ts <- mkT w n t
>     fs <- normal fs
>     let xs = couts w n
>     progLet xs (Splay (wvar i))
>     return (zipWith ((,) . WR . WROut) xs ts,fs)
>   SplitFrom Dn n -> do
>     (is, fs) <- gimme w n fs
>     let cs = couts w n
>     let me = wirev w
>     let o = (WF me, T (map snd is))
>     progLet cs (Splay (wvar (WF me)))
>     for (zip cs is) $ \ (c, (i, _)) -> unify w (WR (WROut c)) i
>     (,) <$> (return <$> normal o) <*> normal fs
>   TupleTo Dn n -> do
>     (is, fs) <- gimme w n fs
>     let c = cout w
>     let o = (WR (WROut c), T (map snd is))
>     progLet [c] (Tup (map (wvar . fst) is))
>     return ([o], fs)
>   TupleTo Up n -> do
>     ([(i, t)], fs) <- gimme w 1 fs
>     ts <- mkT w n t
>     let ws = map WF (wirevs w n)
>     let c = cout w
>     unify w i (WR (WROut c))
>     fs <- normal fs
>     progLet [c] (Tup (map wvar ws))
>     return (zip ws ts, fs)
>   App (k :$: []) -> do
>     gls <- globs <$> stuf
>     case lookup k gls of
>       Nothing -> barf (CBarf (w, "I've never heard of it."))
>       Just (_, ss, its) -> do
>         let xs = nub (foldMap return (ss :-> its)) :: [String]
>         let sub = zip xs (map (V . TF . PC) (couts w (length xs)))
>         let (ss' :-> its') = (ss :-> its) >>= \ x -> case lookup x sub of
>               Just t -> t
>         (gs, hs) <- gimme w (length ss) fs
>         unify w ss' (map snd gs)
>         let cs = couts w (length its')
>         ts <- normal (map snd its')
>         let os = zipWith ((,) . WR . WROut) cs ts
>         progLet cs (Def (PG k) :$ map (wvar . fst) gs)
>         hs <- normal hs
>         return (os, hs)
>   T0 -> return ([(WR (WRV B0), B)], fs)
>   T1 -> return ([(WR (WRV B1), B)], fs)
>   _ -> barf (CBarf (w, "I'm too stupid to understand that just now."))

> tcTiles :: [Signal] -> Int -> [Extent Tile] -> TC [Signal]
> tcTiles [] _ [] = return []
> tcTiles fs l (t : ts) = do
>   (gs, hs) <- tcTile fs (l, t)
>   hs <- tcTiles hs l ts
>   (++) <$> normal gs <*> pure hs
> tcTiles _ l _ = barf (LBarf (l, "I have too many signals for the components."))

> tcCircuit :: [Signal] -> Int -> [[Extent Tile]] -> TC [Signal]
> tcCircuit fs l [] = return fs
> tcCircuit fs l (ts : tss) = do
>   fs <- tcTiles fs l ts
>   tcCircuit fs (l + 1) tss

> type RVar = Either String COut
> deFlex :: Prog COut PVar -> Either WFlex (Prog RVar RVar)
> deFlex (ds, es) =
>   (,) <$> traverse blat ds <*> traverse (traverse ren) es where
>   ren (PF w) = Left w
>   ren (PC c) = Right (Right c)
>   ren (PG s) = Right (Left s)
>   blat (fs, e) = (,) (map Right fs) <$> traverse ren e

> define :: String -> Val -> [Type String] -> [(Latency, Type String)] -> TC ()
> define f v ss lts = TC $ \ s ->
>   Right ((), noStuf {globs = (f, (v, ss, lts)) : globs s})

> gEnv :: [(String, Glob)] -> [(RVar, Val)]
> gEnv = map (\ (s, (v, _, _)) -> (Left s, v))

> tcRaw :: (String, Raw) -> TC ()
> tcRaw (f, Raw ss ics tss ocs lts) | length ss /= length ics
>   = barf (DBarf (f, "Input wires don't match input types."))
> tcRaw (f, Raw ss ics tss ocs lts) | length lts /= length ocs
>   = barf (DBarf (f, "Output wires don't match output types."))
> tcRaw (f, Raw ss ics tss ocs lts) = do
>   let is = zipWith (\ i s -> (WR (WRIn i), fmap TR s)) (below (length ss)) ss
>   let os = map (fmap TR . snd) lts
>   gs <- tcCircuit is 0 tss
>   let es = map (wvar . fst) gs
>   unify (length tss, Extent 0 ("OUTPUTS", T0) 0) (map snd gs) os
>   (ds, _) <- prog <$> stuf
>   case deFlex (ds, es) of
>     Left w -> barf (DBarf (f, "Something's not connected up!"))
>     Right p -> do
>       glos <- globs <$> stuf
>       -- should check latency
>       define f (VF f (oxford (gEnv glos) p)) ss lts
>   return ()

> testGs :: [(String, Glob)]
> testGs =  [  ("and",   (VF "and" andy, [B, B], [(0, B)]))
>           ,  ("not",   (VF "not" noty, [B], [(0, B)]))
>           ,  ("d0c",   (VF "d0c" dexp, [B, B], [(1, B)]))
>           ,  ("csr",   (VF "csr" srff, [B, B, B], [(1, B)]))
>           ,  ("t0c",   (VF "t0c" (oxford myGEnv myT), [B, B], [(1, B)]))
>           ,  ("c4",    (VF "c4"  (oxford myGEnv myC4), [] , replicate 4 (1,B) ))
>           ]

> compile :: [(String, Glob)] -> [(String, Raw)] -> Either Barf [(String, Glob)]
> compile gs rs = do
>   (_, s) <- tc (traverse tcRaw rs) (noStuf {globs = gs})
>   return (globs s)
