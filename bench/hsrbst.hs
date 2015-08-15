-- playing around with STRefs - BST example etc

import Control.Monad.ST
import Data.STRef

-- items in tree (monomorphic, no separate key+value currently)
type Item = Int

-- tree of ints (for simple BST)
-- with STRefs so we can use (monadic) destructive update
-- This leads to an extra level of indirection in data structure plus
-- explicit dealing with refs in all the code traversing trees plus
-- the need for the ST monad everywhere the tree is used:-(
-- Note: the Item in nodes here is not wrapped in a ref (not quite the
-- same as Pawns version)
data DUTree s =
    DUEmpty | DUNode (STRef s (DUTree s)) Item (STRef s (DUTree s))

-- high level version
data Tree = Empty | Node Tree Item Tree
    deriving Show

-- convert list to BST (using destructive insert)
list_dubst :: [Item] -> ST s (DUTree s)
list_dubst xs =
    do
    tp <- newSTRef DUEmpty
    list_dubst_du xs tp
    readSTRef tp

-- As above with (ref to) tree passed in
list_dubst_du :: [Item] -> STRef t (DUTree t) -> ST t ()
list_dubst_du xs tp =
    case xs of
        (x:xs1) ->
            do
            dubst_insert_du x tp
            list_dubst_du xs1 tp
        [] ->
            return ()

-- destructively insert element x into (ref to) BST
dubst_insert_du :: Item -> STRef t (DUTree t) -> ST t ()
dubst_insert_du x tp =
    do
    t <- readSTRef tp
    case t of
        DUEmpty -> -- tp := Node Empty x Empty
            do
            e1 <- newSTRef DUEmpty
            e2 <- newSTRef DUEmpty
            writeSTRef tp (DUNode e1 x e2)
        (DUNode lp n rp) ->
            if x <= n then
                dubst_insert_du x lp
            else
                dubst_insert_du x rp

-- size of tree
-- (doesn't update tree, though this isn't obvious from the type signature)
dubst_size :: DUTree s -> ST s Int
dubst_size t =
    case t of
    DUEmpty ->
        return 0
    (DUNode lp n rp) ->
        do
        l <- readSTRef lp
        sl <- dubst_size l
        r <- readSTRef rp
        sr <- dubst_size r
        return (sl + sr + 1)

-- tests for membership of tree
-- (doesn't update tree, though this isn't obvious from the type signature)
dubst_member :: Item -> DUTree s -> ST s Bool
dubst_member x t =
    case t of
    DUEmpty ->
        return False
    (DUNode lp n rp) ->
        if x == n then
            return True
        else if x <= n then
            do
            l <- readSTRef lp
            dubst_member x l
        else
            do
            r <- readSTRef rp
            dubst_member x r

test1 =
    runST $
    do
    tp <- newSTRef DUEmpty
    dubst_insert_du 3 tp
    dubst_insert_du 5 tp
    t <- readSTRef tp
    dubst_size t

test2 =
    runST $
    do
    t <- list_dubst [3,4,2,5,1]
    dubst_size t

-- illustrates how sharing of (even empty) subtrees breaks insertion
test3 =
    runST $
    do
    tp <- newSTRef DUEmpty -- could be anything
    e1 <- newSTRef DUEmpty
    writeSTRef tp (DUNode e1 5 e1) -- tree with Empty subtree refs shared
    dubst_insert_du 3 tp  -- clobbers both occurrences of e1 - oops!
    t <- readSTRef tp
    dubst_size t

test4 =
    runST $
    do
    t <- list_dubst [3,6,2,5,1]
    -- dubst_member 5 t
    dubst_member 4 t

-- convert from DU tree to high level tree
dubst_bst :: DUTree s -> ST s Tree
dubst_bst t =
    case t of
    DUEmpty ->
        return Empty
    (DUNode lp n rp) ->
        do
        l <- readSTRef lp
        hl <- dubst_bst l
        r <- readSTRef rp
        hr <- dubst_bst r
        return (Node hl n hr)

-- size of high level tree
bst_size :: Tree -> Int
bst_size t =
    case t of
        Empty -> 0
        (Node l _ r) -> (bst_size l) + (bst_size r) + 1

-- size of tree, using conversion to high level tree
dubst_size' :: DUTree s -> ST s Int
dubst_size' t =
    do
    ht <- dubst_bst t
    return (bst_size ht)

-- length of list
len l =
    runST $
    do
    dut <- list_dubst l
    t <- dubst_bst dut
    return $ bst_size t

tst30000 =
    runST $
    do
    t <- list_dubst [1..30000]
    dubst_size t

main = do print tst30000


-- :l "hsrbst"
-- len [3,4,2,5,1]
