import OrderedPartitions.TwoPoleFiniteData.Table
import OrderedPartitions.TwoPoleFiniteBrackets

namespace OrderedPartitions.TwoPoleFinite
set_option maxRecDepth 65536

theorem first_gap_one {n : ℕ} (hn : n<2) :
    RootTracking.OrderedPair (n/2) (row n 2) (row (n+1) 2) := by
  interval_cases n
  · apply stay_pair (B:=[]) (C:=[]) checkedTable (by decide) (by decide) (by decide) (by decide)
    all_goals decide +kernel
  · apply rise_pair (B:=[]) (C:=[(-3,-1)]) checkedTable (by decide) (by decide) (by decide) (by decide)
    all_goals decide +kernel

theorem first_gap_two {n : ℕ} (hn : n<2) :
    RootTracking.OrderedPair (n/2) (row n 2) (row (n+2) 2) := by
  interval_cases n
  · apply rise_pair (B:=[]) (C:=[(-3,-1)]) checkedTable (by decide) (by decide) (by decide) (by decide)
    all_goals decide +kernel
  · apply rise_pair (B:=[]) (C:=[(-1,0)]) checkedTable (by decide) (by decide) (by decide) (by decide)
    all_goals decide +kernel

#print axioms first_gap_one
#print axioms first_gap_two
end OrderedPartitions.TwoPoleFinite
