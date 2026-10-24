import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatCPay022
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem CPay_block_022 (j : Fin 64) (hj : 64*22+j.val < 2540) :
    CPay (64*22+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.CPay_1408
  · exact WuPaper.ClassicalFourthNat.CPay_1409
  · exact WuPaper.ClassicalFourthNat.CPay_1410
  · exact WuPaper.ClassicalFourthNat.CPay_1411
  · exact WuPaper.ClassicalFourthNat.CPay_1412
  · exact WuPaper.ClassicalFourthNat.CPay_1413
  · exact WuPaper.ClassicalFourthNat.CPay_1414
  · exact WuPaper.ClassicalFourthNat.CPay_1415
  · exact WuPaper.ClassicalFourthNat.CPay_1416
  · exact WuPaper.ClassicalFourthNat.CPay_1417
  · exact WuPaper.ClassicalFourthNat.CPay_1418
  · exact WuPaper.ClassicalFourthNat.CPay_1419
  · exact WuPaper.ClassicalFourthNat.CPay_1420
  · exact WuPaper.ClassicalFourthNat.CPay_1421
  · exact WuPaper.ClassicalFourthNat.CPay_1422
  · exact WuPaper.ClassicalFourthNat.CPay_1423
  · exact WuPaper.ClassicalFourthNat.CPay_1424
  · exact WuPaper.ClassicalFourthNat.CPay_1425
  · exact WuPaper.ClassicalFourthNat.CPay_1426
  · exact WuPaper.ClassicalFourthNat.CPay_1427
  · exact WuPaper.ClassicalFourthNat.CPay_1428
  · exact WuPaper.ClassicalFourthNat.CPay_1429
  · exact WuPaper.ClassicalFourthNat.CPay_1430
  · exact WuPaper.ClassicalFourthNat.CPay_1431
  · exact WuPaper.ClassicalFourthNat.CPay_1432
  · exact WuPaper.ClassicalFourthNat.CPay_1433
  · exact WuPaper.ClassicalFourthNat.CPay_1434
  · exact WuPaper.ClassicalFourthNat.CPay_1435
  · exact WuPaper.ClassicalFourthNat.CPay_1436
  · exact WuPaper.ClassicalFourthNat.CPay_1437
  · exact WuPaper.ClassicalFourthNat.CPay_1438
  · exact WuPaper.ClassicalFourthNat.CPay_1439
  · exact WuPaper.ClassicalFourthNat.CPay_1440
  · exact WuPaper.ClassicalFourthNat.CPay_1441
  · exact WuPaper.ClassicalFourthNat.CPay_1442
  · exact WuPaper.ClassicalFourthNat.CPay_1443
  · exact WuPaper.ClassicalFourthNat.CPay_1444
  · exact WuPaper.ClassicalFourthNat.CPay_1445
  · exact WuPaper.ClassicalFourthNat.CPay_1446
  · exact WuPaper.ClassicalFourthNat.CPay_1447
  · exact WuPaper.ClassicalFourthNat.CPay_1448
  · exact WuPaper.ClassicalFourthNat.CPay_1449
  · exact WuPaper.ClassicalFourthNat.CPay_1450
  · exact WuPaper.ClassicalFourthNat.CPay_1451
  · exact WuPaper.ClassicalFourthNat.CPay_1452
  · exact WuPaper.ClassicalFourthNat.CPay_1453
  · exact WuPaper.ClassicalFourthNat.CPay_1454
  · exact WuPaper.ClassicalFourthNat.CPay_1455
  · exact WuPaper.ClassicalFourthNat.CPay_1456
  · exact WuPaper.ClassicalFourthNat.CPay_1457
  · exact WuPaper.ClassicalFourthNat.CPay_1458
  · exact WuPaper.ClassicalFourthNat.CPay_1459
  · exact WuPaper.ClassicalFourthNat.CPay_1460
  · exact WuPaper.ClassicalFourthNat.CPay_1461
  · exact WuPaper.ClassicalFourthNat.CPay_1462
  · exact WuPaper.ClassicalFourthNat.CPay_1463
  · exact WuPaper.ClassicalFourthNat.CPay_1464
  · exact WuPaper.ClassicalFourthNat.CPay_1465
  · exact WuPaper.ClassicalFourthNat.CPay_1466
  · exact WuPaper.ClassicalFourthNat.CPay_1467
  · exact WuPaper.ClassicalFourthNat.CPay_1468
  · exact WuPaper.ClassicalFourthNat.CPay_1469
  · exact WuPaper.ClassicalFourthNat.CPay_1470
  · exact WuPaper.ClassicalFourthNat.CPay_1471
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.CPay_block_022
