module SubList

import public Data.List

%access public export -- FIXME!

-- public export
-- data SubElem : a -> List a -> Type where
--   Z : SubElem a (a :: as)
--   S : SubElem a as -> SubElem a (b :: as)

public export
data SubList : List a -> List a -> Type where
  SubNil : SubList [] xs
  InList : Elem x ys -> SubList xs ys -> SubList (x :: xs) ys

-- Some useful hints for proof construction in polymorphic programs
%hint
public export total
dropFirst : SubList xs ys -> SubList xs (x :: ys)
dropFirst SubNil = SubNil
dropFirst (InList el sub) = InList (There el) (dropFirst sub)

%hint
public export total
subListId : (xs : List a) -> SubList xs xs
subListId [] = SubNil
subListId (x :: xs) = InList Here (dropFirst (subListId xs))

public export total
inSuffix : Elem x ys -> SubList xs ys -> Elem x (zs ++ ys)
inSuffix {zs = []} el sub = el
inSuffix {zs = (x :: xs)} el sub = There (inSuffix el sub)

%hint
public export total
dropPrefix : SubList xs ys -> SubList xs (zs ++ ys)
dropPrefix SubNil = SubNil
dropPrefix (InList el sub) = InList (inSuffix el sub) (dropPrefix sub)

public export total
inPrefix : Elem x ys -> SubList xs ys -> Elem x (ys ++ zs)
inPrefix {zs = []} {ys} el sub
    = rewrite appendNilRightNeutral ys in el
inPrefix {zs = (x :: xs)} Here sub = Here
inPrefix {zs = (x :: xs)} (There y) sub = There (inPrefix y SubNil)

