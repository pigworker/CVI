> module CVIFront where

> import Control.Applicative
> import Data.Char
> import System.FilePath
> import Data.Traversable
> import Data.List

> import CVIParse
> import LLL
> import CVICompile

> data Slice = SB Bit | ST [Slice]
> instance Show Slice where
>   show (SB b) = show b
>   show (ST ss) = ss >>= show

> tempty :: Type String -> Val
> tempty B = VB []
> tempty (T ts) = VT (map tempty ts)

> vconc :: Val -> Val -> Val
> vconc (VB xs) (VB ys) = VB (xs ++ ys)
> vconc (VT us) (VT vs) = VT (zipWith vconc us vs)

> slice :: Slice -> Val
> slice (SB b) = VB [b, b]
> slice (ST ss) = VT (map slice ss)

> behead :: Val -> Maybe (Slice, Val)
> behead (VB (x : _ : xs)) = Just (SB x, VB xs)
> behead (VT vs) = do
>   (ss, vs) <- beheads vs
>   return (ST ss, VT vs)
> behead _ = Nothing

> beheads :: [Val] -> Maybe ([Slice], [Val])
> beheads vs = unzip <$> traverse behead vs

> tyRead :: [Type String] -> String -> Maybe ([Slice], String)
> tyRead [] s = return ([], s)
> tyRead ts (c : s) | isSpace c = tyRead ts s
> tyRead (B : ts) ('0' : s) = do
>   (ss, s) <- tyRead ts s
>   return (SB 0 : ss, s)
> tyRead (B : ts) ('1' : s) = do
>   (ss, s) <- tyRead ts s
>   return (SB 1 : ss, s)
> tyRead (T ts : us) ('(' : s) = do
>   (ss, s) <- tyRead ts s
>   ')' : s <- return $ takeWhile isSpace s
>   (rs, s) <- tyRead us s
>   return (ST ss : rs, s)

> splat :: String -> (String, [Slice]) -> IO ()
> splat f (i, os) = putStrLn (concat [f, " ", i, " -> ", os >>= show])

> cvi :: FilePath -> String -> [String] -> IO ()
> cvi f c is = do
>   tx <- readFile f
>   case cviParse (lines tx) of
>     Left e -> print e
>     Right rs -> do
>       case compile testGs rs of
>         Left b -> print b
>         Right gs ->
>           case lookup c gs of
>             Nothing -> putStrLn ("What's " ++ c ++ ">")
>             Just (VF _ g, ss, _) ->
>               case traverse (tyRead ss) is of
>                 Nothing -> putStrLn "Bad input!"
>                 Just ssjs -> do
>                   let vs = foldr (zipWith vconc) (map tempty ss)
>                             (map (map slice . fst) ssjs)
>                   mapM_ (splat c) (zip is (unfoldr beheads (g vs)))
