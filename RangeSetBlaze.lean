-- Import modules here that should be built as part of the library.
import RangeSetBlaze.Basic
import RangeSetBlaze.AlgoA
import RangeSetBlaze.AlgoAMap
import RangeSetBlaze.AlgoCMap
import RangeSetBlaze.AlgoB
import RangeSetBlaze.AlgoC
import RangeSetBlaze.AlgoCLen
import RangeSetBlaze.AlgoD
import RangeSetBlaze.AlgoDMap

-- Export main types and definitions
export IntRange (toSet empty nonempty)
export RangeSetBlaze (toSet internalAddA internalAddB internalAddC internalAddCLen internalAddD)
export RangeMapBlaze (internalAddAMap internalAddCMap internalAddDMap)
