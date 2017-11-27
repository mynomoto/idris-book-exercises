import Data.List.Views

%default total

data SplitList : List a -> Type where
     SplitNil : SplitList []
     SplitOne : SplitList [x]
     SplitPair : (lefts : List a) -> (rights : List a) -> SplitList (lefts ++ rights)

splitList : (input : List a) -> SplitList input
splitList input = splitListHelper input input where
  splitListHelper : List a -> (input : List a) -> SplitList input
  splitListHelper _ [] = SplitNil
  splitListHelper _ [x] = SplitOne
  splitListHelper (_ :: _ :: counter) (item :: items) =
    case splitListHelper counter items of
         SplitNil => SplitOne
         SplitOne {x} => SplitPair [item] [x]
         SplitPair lefts rights => SplitPair (item :: lefts) rights
  splitListHelper _ items = SplitPair [] items

partial
mergeSortPartial : Ord a => List a -> List a
mergeSortPartial xs with (splitList xs)
  mergeSortPartial [] | SplitNil = []
  mergeSortPartial [x] | SplitOne = [x]
  mergeSortPartial (lefts ++ rights) | (SplitPair lefts rights) = merge (mergeSortPartial lefts) (mergeSortPartial rights)

mergeSort : Ord a => List a -> List a
mergeSort input with (splitRec input)
  mergeSort [] | SplitRecNil = []
  mergeSort [x] | SplitRecOne = [x]
  mergeSort (lefts ++ rights) | (SplitRecPair lrec rrec) = merge (mergeSort lefts | lrec) (mergeSort rights | rrec)

