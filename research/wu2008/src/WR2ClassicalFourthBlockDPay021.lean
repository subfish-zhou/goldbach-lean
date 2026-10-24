import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatDPay021
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem DPay_block_021 (j : Fin 64) (hj : 64*21+j.val < 2540) :
    DPay (64*21+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.DPay_1344
  · exact WuPaper.ClassicalFourthNat.DPay_1345
  · exact WuPaper.ClassicalFourthNat.DPay_1346
  · exact WuPaper.ClassicalFourthNat.DPay_1347
  · exact WuPaper.ClassicalFourthNat.DPay_1348
  · exact WuPaper.ClassicalFourthNat.DPay_1349
  · exact WuPaper.ClassicalFourthNat.DPay_1350
  · exact WuPaper.ClassicalFourthNat.DPay_1351
  · exact WuPaper.ClassicalFourthNat.DPay_1352
  · exact WuPaper.ClassicalFourthNat.DPay_1353
  · exact WuPaper.ClassicalFourthNat.DPay_1354
  · exact WuPaper.ClassicalFourthNat.DPay_1355
  · exact WuPaper.ClassicalFourthNat.DPay_1356
  · exact WuPaper.ClassicalFourthNat.DPay_1357
  · exact WuPaper.ClassicalFourthNat.DPay_1358
  · exact WuPaper.ClassicalFourthNat.DPay_1359
  · exact WuPaper.ClassicalFourthNat.DPay_1360
  · exact WuPaper.ClassicalFourthNat.DPay_1361
  · exact WuPaper.ClassicalFourthNat.DPay_1362
  · exact WuPaper.ClassicalFourthNat.DPay_1363
  · exact WuPaper.ClassicalFourthNat.DPay_1364
  · exact WuPaper.ClassicalFourthNat.DPay_1365
  · exact WuPaper.ClassicalFourthNat.DPay_1366
  · exact WuPaper.ClassicalFourthNat.DPay_1367
  · exact WuPaper.ClassicalFourthNat.DPay_1368
  · exact WuPaper.ClassicalFourthNat.DPay_1369
  · exact WuPaper.ClassicalFourthNat.DPay_1370
  · exact WuPaper.ClassicalFourthNat.DPay_1371
  · exact WuPaper.ClassicalFourthNat.DPay_1372
  · exact WuPaper.ClassicalFourthNat.DPay_1373
  · exact WuPaper.ClassicalFourthNat.DPay_1374
  · exact WuPaper.ClassicalFourthNat.DPay_1375
  · exact WuPaper.ClassicalFourthNat.DPay_1376
  · exact WuPaper.ClassicalFourthNat.DPay_1377
  · exact WuPaper.ClassicalFourthNat.DPay_1378
  · exact WuPaper.ClassicalFourthNat.DPay_1379
  · exact WuPaper.ClassicalFourthNat.DPay_1380
  · exact WuPaper.ClassicalFourthNat.DPay_1381
  · exact WuPaper.ClassicalFourthNat.DPay_1382
  · exact WuPaper.ClassicalFourthNat.DPay_1383
  · exact WuPaper.ClassicalFourthNat.DPay_1384
  · exact WuPaper.ClassicalFourthNat.DPay_1385
  · exact WuPaper.ClassicalFourthNat.DPay_1386
  · exact WuPaper.ClassicalFourthNat.DPay_1387
  · exact WuPaper.ClassicalFourthNat.DPay_1388
  · exact WuPaper.ClassicalFourthNat.DPay_1389
  · exact WuPaper.ClassicalFourthNat.DPay_1390
  · exact WuPaper.ClassicalFourthNat.DPay_1391
  · exact WuPaper.ClassicalFourthNat.DPay_1392
  · exact WuPaper.ClassicalFourthNat.DPay_1393
  · exact WuPaper.ClassicalFourthNat.DPay_1394
  · exact WuPaper.ClassicalFourthNat.DPay_1395
  · exact WuPaper.ClassicalFourthNat.DPay_1396
  · exact WuPaper.ClassicalFourthNat.DPay_1397
  · exact WuPaper.ClassicalFourthNat.DPay_1398
  · exact WuPaper.ClassicalFourthNat.DPay_1399
  · exact WuPaper.ClassicalFourthNat.DPay_1400
  · exact WuPaper.ClassicalFourthNat.DPay_1401
  · exact WuPaper.ClassicalFourthNat.DPay_1402
  · exact WuPaper.ClassicalFourthNat.DPay_1403
  · exact WuPaper.ClassicalFourthNat.DPay_1404
  · exact WuPaper.ClassicalFourthNat.DPay_1405
  · exact WuPaper.ClassicalFourthNat.DPay_1406
  · exact WuPaper.ClassicalFourthNat.DPay_1407
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.DPay_block_021
