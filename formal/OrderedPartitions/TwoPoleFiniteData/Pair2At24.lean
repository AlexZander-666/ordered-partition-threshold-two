import OrderedPartitions.TwoPoleFiniteBrackets
import OrderedPartitions.TwoPoleFiniteData.Table

namespace OrderedPartitions.TwoPoleFinite

set_option maxHeartbeats 0
set_option maxRecDepth 65536


private def lowerBoxes : Boxes := [(-2039/9,-1019/5), (-1965/83,-491/21), (-913/111,-1825/223), (-409/103,-1635/413), (-709/315,-1417/631), (-1193/855,-149/107), (-491/533,-981/1067), (-25/39,-799/1249), (-327/697,-653/1395), (-545/1503,-17/47), (-59/197,-471/1577), (-215/809,-429/1619)]
private def upperBoxes : Boxes := [(-255,-2039/9), (-1977/71,-247/9), (-29/3,-1855/193), (-845/179,-1689/359), (-747/277,-1493/555), (-1285/763,-321/191), (-541/483,-1081/967), (-449/575,-897/1151), (-371/653,-741/1307), (-309/715,-617/1431), (-263/761,-525/1523), (-29/99,-463/1585), (-107/405,-427/1621)]

theorem checkedPair2At24 : RootTracking.OrderedPair 12 (row 24 2) (row 26 2) := by
  apply rise_pair (B:=lowerBoxes) (C:=upperBoxes) checkedTable (by decide) (by decide) (by decide) (by decide)
  · decide +kernel
  · decide +kernel
  · decide +kernel

end OrderedPartitions.TwoPoleFinite
