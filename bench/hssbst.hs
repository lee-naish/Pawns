-- Haskell version of bst.ps with `seq` to try to improve performance

data Bst = Mt | Node Bst Int Bst
type Ints = [Int]

list_bst :: Ints -> Bst
list_bst xs = list_bst_acc xs Mt

list_bst_acc :: Ints -> Bst -> Bst
list_bst_acc xs t0 =
    case xs of
        (x:xs1) ->
            let t1 = bst_insert x t0
            in t1 `seq` list_bst_acc xs1 t1
        [] -> t0

bst_insert :: Int -> Bst -> Bst
bst_insert x t0 =
    case t0 of
        Mt -> Node Mt x Mt
        (Node l n r) ->
            if x <= n then    
                let t1 = bst_insert x l
                in t1 `seq` Node t1 n r
            else
                let t1 = bst_insert x r
                in t1 `seq` Node l n t1

bst_size :: Bst -> Int
bst_size t =
    case t of
        Mt -> 0
        (Node l n r) -> 1 + (bst_size l) + (bst_size r)

tst = bst_size (list_bst [1..10])

main = do print (bst_size (list_bst [1..30000]))
-- C;ghc -O3 hsbst.hs ; time ./hsbst
-- [1 of 1] Compiling Main             ( hsbst.hs, hsbst.o )
-- Linking hsbst ...
-- 10000
-- 
-- real    0m11.908s
-- user    0m11.855s
-- sys 0m0.028s
-- C;ghc -O3 hsbst.hs ; time ./hsbst
-- [1 of 1] Compiling Main             ( hsbst.hs, hsbst.o )
-- Linking hsbst ...
-- 30000
-- 
-- real    3m50.300s
-- user    3m49.509s
-- sys 0m0.280s


