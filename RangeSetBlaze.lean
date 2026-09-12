-- Import modules here that should be built as part of the library.
import RangeSetBlaze.Basic
import RangeSetBlaze.AlgoA
import RangeSetBlaze.AlgoAMap
import RangeSetBlaze.AlgoCMap
import RangeSetBlaze.AlgoB
import RangeSetBlaze.AlgoC
import RangeSetBlaze.AlgoD

-- Export main types and definitions
export IntRange (toSet empty nonempty)
export RangeSetBlaze (toSet internalAddA internalAddB internalAddC internalAddD)
export RangeMapBlaze (internalAddAMap internalAddCMap)
