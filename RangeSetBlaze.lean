-- Import modules here that should be built as part of the library.
import RangeSetBlaze.Basic
import RangeSetBlaze.AlgoA
import RangeSetBlaze.AlgoAMap
import RangeSetBlaze.AlgoCMap
import RangeSetBlaze.AlgoB
import RangeSetBlaze.AlgoC
import RangeSetBlaze.AlgoD
import RangeSetBlaze.AlgoDMap
import RangeSetBlaze.AlgoE
import RangeSetBlaze.AlgoELen
import RangeSetBlaze.CrossAlgorithm
import RangeSetBlaze.Query

-- Export main types and definitions
export IntRange (toSet empty nonempty)
export RangeSetBlaze (toSet internalAddA internalAddB internalAddC internalAddCLen internalAddD
  internalAddDLen internalAddE internalAddELen)
export RangeMapBlaze (internalAddAMap internalAddCMap internalAddDMap)
