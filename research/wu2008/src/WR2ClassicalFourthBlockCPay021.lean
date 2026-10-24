import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatCPay021
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem CPay_block_021 (j : Fin 64) (hj : 64*21+j.val < 2540) :
    CPay (64*21+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.CPay_1344
  · exact WuPaper.ClassicalFourthNat.CPay_1345
  · exact WuPaper.ClassicalFourthNat.CPay_1346
  · exact WuPaper.ClassicalFourthNat.CPay_1347
  · exact WuPaper.ClassicalFourthNat.CPay_1348
  · exact WuPaper.ClassicalFourthNat.CPay_1349
  · exact WuPaper.ClassicalFourthNat.CPay_1350
  · exact WuPaper.ClassicalFourthNat.CPay_1351
  · exact WuPaper.ClassicalFourthNat.CPay_1352
  · exact WuPaper.ClassicalFourthNat.CPay_1353
  · exact WuPaper.ClassicalFourthNat.CPay_1354
  · exact WuPaper.ClassicalFourthNat.CPay_1355
  · exact WuPaper.ClassicalFourthNat.CPay_1356
  · exact WuPaper.ClassicalFourthNat.CPay_1357
  · exact WuPaper.ClassicalFourthNat.CPay_1358
  · exact WuPaper.ClassicalFourthNat.CPay_1359
  · exact WuPaper.ClassicalFourthNat.CPay_1360
  · exact WuPaper.ClassicalFourthNat.CPay_1361
  · exact WuPaper.ClassicalFourthNat.CPay_1362
  · exact WuPaper.ClassicalFourthNat.CPay_1363
  · exact WuPaper.ClassicalFourthNat.CPay_1364
  · exact WuPaper.ClassicalFourthNat.CPay_1365
  · exact WuPaper.ClassicalFourthNat.CPay_1366
  · exact WuPaper.ClassicalFourthNat.CPay_1367
  · exact WuPaper.ClassicalFourthNat.CPay_1368
  · exact WuPaper.ClassicalFourthNat.CPay_1369
  · exact WuPaper.ClassicalFourthNat.CPay_1370
  · exact WuPaper.ClassicalFourthNat.CPay_1371
  · exact WuPaper.ClassicalFourthNat.CPay_1372
  · exact WuPaper.ClassicalFourthNat.CPay_1373
  · exact WuPaper.ClassicalFourthNat.CPay_1374
  · exact WuPaper.ClassicalFourthNat.CPay_1375
  · exact WuPaper.ClassicalFourthNat.CPay_1376
  · exact WuPaper.ClassicalFourthNat.CPay_1377
  · exact WuPaper.ClassicalFourthNat.CPay_1378
  · exact WuPaper.ClassicalFourthNat.CPay_1379
  · exact WuPaper.ClassicalFourthNat.CPay_1380
  · exact WuPaper.ClassicalFourthNat.CPay_1381
  · exact WuPaper.ClassicalFourthNat.CPay_1382
  · exact WuPaper.ClassicalFourthNat.CPay_1383
  · exact WuPaper.ClassicalFourthNat.CPay_1384
  · exact WuPaper.ClassicalFourthNat.CPay_1385
  · exact WuPaper.ClassicalFourthNat.CPay_1386
  · exact WuPaper.ClassicalFourthNat.CPay_1387
  · exact WuPaper.ClassicalFourthNat.CPay_1388
  · exact WuPaper.ClassicalFourthNat.CPay_1389
  · exact WuPaper.ClassicalFourthNat.CPay_1390
  · exact WuPaper.ClassicalFourthNat.CPay_1391
  · exact WuPaper.ClassicalFourthNat.CPay_1392
  · exact WuPaper.ClassicalFourthNat.CPay_1393
  · exact WuPaper.ClassicalFourthNat.CPay_1394
  · exact WuPaper.ClassicalFourthNat.CPay_1395
  · exact WuPaper.ClassicalFourthNat.CPay_1396
  · exact WuPaper.ClassicalFourthNat.CPay_1397
  · exact WuPaper.ClassicalFourthNat.CPay_1398
  · exact WuPaper.ClassicalFourthNat.CPay_1399
  · exact WuPaper.ClassicalFourthNat.CPay_1400
  · exact WuPaper.ClassicalFourthNat.CPay_1401
  · exact WuPaper.ClassicalFourthNat.CPay_1402
  · exact WuPaper.ClassicalFourthNat.CPay_1403
  · exact WuPaper.ClassicalFourthNat.CPay_1404
  · exact WuPaper.ClassicalFourthNat.CPay_1405
  · exact WuPaper.ClassicalFourthNat.CPay_1406
  · exact WuPaper.ClassicalFourthNat.CPay_1407
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.CPay_block_021
