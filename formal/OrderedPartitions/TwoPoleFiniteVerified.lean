import OrderedPartitions.TwoPoleFiniteData.Pair1At02
import OrderedPartitions.TwoPoleFiniteData.Pair1At03
import OrderedPartitions.TwoPoleFiniteData.Pair1At04
import OrderedPartitions.TwoPoleFiniteData.Pair1At05
import OrderedPartitions.TwoPoleFiniteData.Pair1At06
import OrderedPartitions.TwoPoleFiniteData.Pair1At07
import OrderedPartitions.TwoPoleFiniteData.Pair1At08
import OrderedPartitions.TwoPoleFiniteData.Pair1At09
import OrderedPartitions.TwoPoleFiniteData.Pair1At10
import OrderedPartitions.TwoPoleFiniteData.Pair1At11
import OrderedPartitions.TwoPoleFiniteData.Pair1At12
import OrderedPartitions.TwoPoleFiniteData.Pair1At13
import OrderedPartitions.TwoPoleFiniteData.Pair1At14
import OrderedPartitions.TwoPoleFiniteData.Pair1At15
import OrderedPartitions.TwoPoleFiniteData.Pair1At16
import OrderedPartitions.TwoPoleFiniteData.Pair1At17
import OrderedPartitions.TwoPoleFiniteData.Pair1At18
import OrderedPartitions.TwoPoleFiniteData.Pair1At19
import OrderedPartitions.TwoPoleFiniteData.Pair1At20
import OrderedPartitions.TwoPoleFiniteData.Pair1At21
import OrderedPartitions.TwoPoleFiniteData.Pair2At02
import OrderedPartitions.TwoPoleFiniteData.Pair2At03
import OrderedPartitions.TwoPoleFiniteData.Pair2At04
import OrderedPartitions.TwoPoleFiniteData.Pair2At05
import OrderedPartitions.TwoPoleFiniteData.Pair2At06
import OrderedPartitions.TwoPoleFiniteData.Pair2At07
import OrderedPartitions.TwoPoleFiniteData.Pair2At08
import OrderedPartitions.TwoPoleFiniteData.Pair2At09
import OrderedPartitions.TwoPoleFiniteData.Pair2At10
import OrderedPartitions.TwoPoleFiniteData.Pair2At11
import OrderedPartitions.TwoPoleFiniteData.Pair2At12
import OrderedPartitions.TwoPoleFiniteData.Pair2At13
import OrderedPartitions.TwoPoleFiniteData.Pair2At14
import OrderedPartitions.TwoPoleFiniteData.Pair2At15
import OrderedPartitions.TwoPoleFiniteData.Pair2At16
import OrderedPartitions.TwoPoleFiniteData.Pair2At17
import OrderedPartitions.TwoPoleFiniteData.Pair2At18
import OrderedPartitions.TwoPoleFiniteData.Pair2At19
import OrderedPartitions.TwoPoleFiniteData.Pair2At20
import OrderedPartitions.TwoPoleFiniteData.Pair2At21
import OrderedPartitions.TwoPoleFiniteData.Pair2At22
import OrderedPartitions.TwoPoleFiniteData.Pair2At23
import OrderedPartitions.TwoPoleFiniteData.Pair2At24
import OrderedPartitions.TwoPoleFiniteData.Pair2At25
import OrderedPartitions.TwoPoleFiniteData.Pair2At26
import OrderedPartitions.TwoPoleFiniteData.Pair2At27

namespace OrderedPartitions.TwoPoleFinite

set_option maxHeartbeats 0
set_option maxRecDepth 65536

theorem original_gap1_finite (n : ℕ) (lo : 2≤n) (hi : n≤21) :
    RootTracking.OrderedPair (n/2) (row n 2) (row (n+1) 2) := by
  interval_cases n
  · exact checkedPair1At02
  · exact checkedPair1At03
  · exact checkedPair1At04
  · exact checkedPair1At05
  · exact checkedPair1At06
  · exact checkedPair1At07
  · exact checkedPair1At08
  · exact checkedPair1At09
  · exact checkedPair1At10
  · exact checkedPair1At11
  · exact checkedPair1At12
  · exact checkedPair1At13
  · exact checkedPair1At14
  · exact checkedPair1At15
  · exact checkedPair1At16
  · exact checkedPair1At17
  · exact checkedPair1At18
  · exact checkedPair1At19
  · exact checkedPair1At20
  · exact checkedPair1At21

#print axioms original_gap1_finite

theorem original_gap2_finite (n : ℕ) (lo : 2≤n) (hi : n≤27) :
    RootTracking.OrderedPair (n/2) (row n 2) (row (n+2) 2) := by
  interval_cases n
  · exact checkedPair2At02
  · exact checkedPair2At03
  · exact checkedPair2At04
  · exact checkedPair2At05
  · exact checkedPair2At06
  · exact checkedPair2At07
  · exact checkedPair2At08
  · exact checkedPair2At09
  · exact checkedPair2At10
  · exact checkedPair2At11
  · exact checkedPair2At12
  · exact checkedPair2At13
  · exact checkedPair2At14
  · exact checkedPair2At15
  · exact checkedPair2At16
  · exact checkedPair2At17
  · exact checkedPair2At18
  · exact checkedPair2At19
  · exact checkedPair2At20
  · exact checkedPair2At21
  · exact checkedPair2At22
  · exact checkedPair2At23
  · exact checkedPair2At24
  · exact checkedPair2At25
  · exact checkedPair2At26
  · exact checkedPair2At27

#print axioms original_gap2_finite

end OrderedPartitions.TwoPoleFinite
