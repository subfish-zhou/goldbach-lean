import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatouterPay021
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem outerPay_block_021 (j : Fin 64) (hj : 64*21+j.val < 10540) :
    OuterPay (64*21+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.outerPay_1344
  · exact WuPaper.ClassicalFourthNat.outerPay_1345
  · exact WuPaper.ClassicalFourthNat.outerPay_1346
  · exact WuPaper.ClassicalFourthNat.outerPay_1347
  · exact WuPaper.ClassicalFourthNat.outerPay_1348
  · exact WuPaper.ClassicalFourthNat.outerPay_1349
  · exact WuPaper.ClassicalFourthNat.outerPay_1350
  · exact WuPaper.ClassicalFourthNat.outerPay_1351
  · exact WuPaper.ClassicalFourthNat.outerPay_1352
  · exact WuPaper.ClassicalFourthNat.outerPay_1353
  · exact WuPaper.ClassicalFourthNat.outerPay_1354
  · exact WuPaper.ClassicalFourthNat.outerPay_1355
  · exact WuPaper.ClassicalFourthNat.outerPay_1356
  · exact WuPaper.ClassicalFourthNat.outerPay_1357
  · exact WuPaper.ClassicalFourthNat.outerPay_1358
  · exact WuPaper.ClassicalFourthNat.outerPay_1359
  · exact WuPaper.ClassicalFourthNat.outerPay_1360
  · exact WuPaper.ClassicalFourthNat.outerPay_1361
  · exact WuPaper.ClassicalFourthNat.outerPay_1362
  · exact WuPaper.ClassicalFourthNat.outerPay_1363
  · exact WuPaper.ClassicalFourthNat.outerPay_1364
  · exact WuPaper.ClassicalFourthNat.outerPay_1365
  · exact WuPaper.ClassicalFourthNat.outerPay_1366
  · exact WuPaper.ClassicalFourthNat.outerPay_1367
  · exact WuPaper.ClassicalFourthNat.outerPay_1368
  · exact WuPaper.ClassicalFourthNat.outerPay_1369
  · exact WuPaper.ClassicalFourthNat.outerPay_1370
  · exact WuPaper.ClassicalFourthNat.outerPay_1371
  · exact WuPaper.ClassicalFourthNat.outerPay_1372
  · exact WuPaper.ClassicalFourthNat.outerPay_1373
  · exact WuPaper.ClassicalFourthNat.outerPay_1374
  · exact WuPaper.ClassicalFourthNat.outerPay_1375
  · exact WuPaper.ClassicalFourthNat.outerPay_1376
  · exact WuPaper.ClassicalFourthNat.outerPay_1377
  · exact WuPaper.ClassicalFourthNat.outerPay_1378
  · exact WuPaper.ClassicalFourthNat.outerPay_1379
  · exact WuPaper.ClassicalFourthNat.outerPay_1380
  · exact WuPaper.ClassicalFourthNat.outerPay_1381
  · exact WuPaper.ClassicalFourthNat.outerPay_1382
  · exact WuPaper.ClassicalFourthNat.outerPay_1383
  · exact WuPaper.ClassicalFourthNat.outerPay_1384
  · exact WuPaper.ClassicalFourthNat.outerPay_1385
  · exact WuPaper.ClassicalFourthNat.outerPay_1386
  · exact WuPaper.ClassicalFourthNat.outerPay_1387
  · exact WuPaper.ClassicalFourthNat.outerPay_1388
  · exact WuPaper.ClassicalFourthNat.outerPay_1389
  · exact WuPaper.ClassicalFourthNat.outerPay_1390
  · exact WuPaper.ClassicalFourthNat.outerPay_1391
  · exact WuPaper.ClassicalFourthNat.outerPay_1392
  · exact WuPaper.ClassicalFourthNat.outerPay_1393
  · exact WuPaper.ClassicalFourthNat.outerPay_1394
  · exact WuPaper.ClassicalFourthNat.outerPay_1395
  · exact WuPaper.ClassicalFourthNat.outerPay_1396
  · exact WuPaper.ClassicalFourthNat.outerPay_1397
  · exact WuPaper.ClassicalFourthNat.outerPay_1398
  · exact WuPaper.ClassicalFourthNat.outerPay_1399
  · exact WuPaper.ClassicalFourthNat.outerPay_1400
  · exact WuPaper.ClassicalFourthNat.outerPay_1401
  · exact WuPaper.ClassicalFourthNat.outerPay_1402
  · exact WuPaper.ClassicalFourthNat.outerPay_1403
  · exact WuPaper.ClassicalFourthNat.outerPay_1404
  · exact WuPaper.ClassicalFourthNat.outerPay_1405
  · exact WuPaper.ClassicalFourthNat.outerPay_1406
  · exact WuPaper.ClassicalFourthNat.outerPay_1407
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.outerPay_block_021
