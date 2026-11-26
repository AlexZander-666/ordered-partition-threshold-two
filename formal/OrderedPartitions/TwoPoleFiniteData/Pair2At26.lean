import OrderedPartitions.TwoPoleFiniteBrackets
import OrderedPartitions.TwoPoleFiniteData.Table

namespace OrderedPartitions.TwoPoleFinite

set_option maxHeartbeats 0
set_option maxRecDepth 65536


private def lowerBoxes : Boxes := [(-255,-2039/9), (-1977/71,-247/9), (-29/3,-1855/193), (-845/179,-1689/359), (-747/277,-1493/555), (-1285/763,-321/191), (-541/483,-1081/967), (-449/575,-897/1151), (-371/653,-741/1307), (-309/715,-617/1431), (-263/761,-525/1523), (-29/99,-463/1585), (-107/405,-427/1621)]
private def upperBoxes : Boxes := [(-1021/3,-2041/7), (-993/31,-1985/63), (-1881/167,-235/21), (-867/157,-1733/315), (-1557/491,-389/123), (-683/341,-1365/683), (-1173/875,-293/219), (-991/1057,-495/529), (-415/609,-829/1219), (-87/169,-695/1353), (-295/729,-589/1459), (-511/1537,-255/769), (-229/795,-457/1591), (-427/1621,-213/811)]

theorem checkedPair2At26 : RootTracking.OrderedPair 13 (row 26 2) (row 28 2) := by
  apply rise_pair (B:=lowerBoxes) (C:=upperBoxes) checkedTable (by decide) (by decide) (by decide) (by decide)
  · decide +kernel
  · decide +kernel
  · decide +kernel

end OrderedPartitions.TwoPoleFinite
