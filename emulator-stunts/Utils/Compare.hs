import Data.List
import Data.Char
import Data.Maybe
import Data.Function
import Control.Applicative
import Control.Monad
import qualified Data.IntSet as S
import System.IO

my = "LOG.TXT"
ref = "../restunts/stunts/LOGCPU0.TXT"

ints = do
    hSetBuffering stdout NoBuffering
    f <- ref'
    let f' = map snd f
    print $ snd $ mapAccumL acc 0 $ filter (fst . snd) $ zip [0..] $ map k $ zip3 f' (undefined: f') (tails f)
  where
    inst (_,i,_,_,_) = i
    hasrep (_,(i,_),_,_,_) = "rep" `isPrefixOf` i
    (p,_,_,_,_) `at` q  = p == q
    k (a,b,xx) = (a `at` ("20B0","1909"), (hasrep b && inst b == inst c, length as + 1, m))
        where (as,_:(m, c):_) = span (not . (`at` ("20B0","1999")) . snd) xx
    acc st (n,(_,(b,l,m))) = (st - fromEnum b, (n + st, [((n + st, n + st + l), m) | b]))

ref' = map head . groupBy (repe `on` snd) . filter (not . isFar) . catMaybes . map hh . mapSnd parse . zip [0..] . lines <$> readFile ref

main' = ints
main = do
    is <- concatMap (snd :: (Int,a) -> a) . read <$> readFile "interrupts2.txt"
    let set= concatMap ((\(a,b)->[a..b]) . fst) is
{-            [85058..85668]
         ++ [86597..87218]
         ++ [88176..88786]
         ++ [89715..90325]
         ++ [91288..91898] -}
    f1 <- readFile my
    f2 <- filter (not . isFar__ (S.fromList $ map snd is{-[85876,87454,89039,90592]-})) <$> ref'
    comp_ (S.fromList set) (filter (not . isFar) $ catMaybes $ map hh $ mapSnd parse $ zip [0..] $ drop 5 $ lines f1)
         f2

showCtx n m = do
    f1 <- readFile my
    putStrLn $ unlines $ take 10 $ drop (n-9) $ drop 5 $ lines f1
    f2 <- readFile ref
    putStrLn $ unlines $ take 10 $ drop (m-9) $ lines f2

hh (a, Just b) = Just (a, b)
hh _ = Nothing
mapSnd f = map (\(a,b) -> (a, f b))

takes [] [] = []
takes (i:is) s = take i s: takes is (drop i s)

parse = gg . ff

ff = takes [4,5,4,2,5,50
           ,4,8 ,5,8 ,5,8 ,5,8 ,5,8 ,5,8 ,5,8 ,5,8
           ,4,4 ,4,4 ,4,4 ,4,4 ,4,4
           ,4,1,4,1,4,1,4,1,4,1,4,1,4,1]
gg [cs,":0000",ip,"  ",op,args
     ,"EAX:",ax," EBX:",bx," ECX:",cx," EDX:",dx," ESI:",si," EDI:",di," EBP:",bp," ESP:",sp
     ," DS:",ds," ES:",es," FS:",fs," GS:",gs," SS:",ss
     ," CF:",c," ZF:",z," SF:",s," OF:",o," AF:",a," PF:",p," IF:",i
     ]
    = Just ((cs,ip),(corr op,args),(ax,bx,cx,dx,si,di,bp,sp),(ds,es,fs,gs,ss),(c,z,s,o,a,p,i))
  where
    corr x = x
gg x = Nothing --error $ show x

pr ((cs,ip),(op,args),(ax,bx,cx,dx,si,di,bp,sp),(ds,es,fs,gs,ss),(c,z,s,o,a,p,i))
  = concat
    [cs,":0000",ip,"  ",op,args
    ,"EAX:",ax," EBX:",bx," ECX:",cx," EDX:",dx," ESI:",si," EDI:",di," EBP:",bp," ESP:",sp
    ," DS:",ds," ES:",es," FS:",fs," GS:",gs," SS:",ss
    ," CF:",c," ZF:",z," SF:",s," OF:",o," AF:",a," PF:",p," IF:",i
    ]

repe (x,_,_,_,_) (y,_,_,_,_) = x == y

isFar__ s (n, ((cs,_),_,_,_,_)) = n `S.member` s

isFar (n, ((cs,_),_,_,_,_)) = cs `elem` ["C7FF","F000"]

betw a b c = a <= c && c <= b
readH [a,b] = digitToInt a * 16 + digitToInt b

comp_ set xs ys = comp (map correct xs) ys
  where
    correct x@(n,_) | n `S.member` (S.fromList $ [177,178,181,182,486,487,489,490,3173,3174,3226,3227,33041]) = noflag x
    correct x@(n,_) | n `S.member` (S.fromList $ [1199,3733,3734,3735,33036,33037,33038,33039 ,141638,141639,141640,141641, 182534,182535,182536,182537]) = noflag $ anny x
    correct x@(n,_) | n `S.member` set = noflag $ anny' x
    correct a = a

annnny (n,(_,_,y,z,v)) = (n, (("?","?"), ("?","?"),y,z,v))
anny (n,(a1,b1,_,_,fs)) = (n,(a1,b1,("?","?","?","?","?","?","?","?"),("?","?","?","?","?"),fs))
anny' (n,(a1,b1,(ax,bx,cx,dx,si,di,bp,sp),(ds,es,fs,gs,ss),c1)) = (n,(a1,b1,("?",bx,"?",dx,si,"?",bp,sp),(ds,es,fs,gs,ss),c1))
noflag (n,(a1,b1,c1,d1,(c,z,s,o,a,p,i))) = (n,(a1,b1,c1,d1,("?","?","?","?","?","?",i)))


comp
  ((n,aa@((cs,ip),(op,args),(ax,bx,cx,dx,si,di,bp,sp),(ds,es,fs,gs,ss),(c,z,s,o,a,p,i))): xs)
  ((n',bb@((cs',ip'),(op',args'),(ax',bx',cx',dx',si',di',bp',sp'),(ds',es',fs',gs',ss'),(c',z',s',o',a',p',i'))): ys)
  | null xs || null ys || not 
   ( cs ~= cs'
  && ip ~= ip'
  && op ~= op'
  && ax ~= ax'
  && bx ~= bx'
  && cx ~= cx'
  && dx ~= dx'
  && si ~= si'
  && di ~= di'
  && bp ~= bp'
  && sp ~= sp'
  && ds ~= ds'
  && es ~= es'
  && fs ~= fs'
  && gs ~= gs'
  && ss ~= ss'
  && c ~= c'
  && z ~= z'
  && s ~= s'
  && o ~= o'
  && a ~= a'
  && p ~= p'
  && i ~= i'
   )
  = do
    showCtx n n'
    when (null xs) $ print "xs ended!"
    when (null ys) $ print "ys ended!"
    putStrLn $ show n ++ "   " ++ show n' ++ "\n" ++ show aa ++ "\n" ++ show bb
comp ((n,_): xs) (_: ys) = do
    when ((n `mod` 10000) == 0) $ print n
    comp xs ys
comp _ _ = do
    putStrLn $  " lines ok!"


infix 4 ~=
('?':_) ~= _ = True
xs ~= ys = xs == ys

