import OrderedPartitions.TwoPoleFiniteBrackets
import OrderedPartitions.TwoPoleFiniteData.Table

namespace OrderedPartitions.TwoPoleFinite

set_option maxHeartbeats 0
set_option maxRecDepth 65536


private def lowerBoxes : Boxes := [(-1019/5,-509/3), (-975/49,-487/25), (-447/65,-893/131), (-785/239,-49/15), (-83/45,-663/361), (-17/15,-543/481), (-437/587,-109/147), (-175/337,-349/675), (-285/739,-71/185), (-241/783,-15/49), (-217/807,-27/101)]
private def upperBoxes : Boxes := [(-255,-1019/5), (-983/41,-491/21), (-913/111,-57/7), (-409/103,-817/207), (-709/315,-177/79), (-597/427,-149/107), (-491/533,-245/267), (-25/39,-399/625), (-327/697,-163/349), (-273/751,-17/47), (-59/197,-235/789), (-215/809,-107/405)]

theorem checkedPair2At22 : RootTracking.OrderedPair 11 (row 22 2) (row 24 2) := by
  apply rise_pair (B:=lowerBoxes) (C:=upperBoxes) checkedTable (by decide) (by decide) (by decide) (by decide)
  · decide +kernel
  · decide +kernel
  · decide +kernel

end OrderedPartitions.TwoPoleFinite
