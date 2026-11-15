import HodgeLean.Foundations.Program.HurwitzPrymRexG32Core
import HodgeLean.Foundations.Program.G32PropFourSixPacked0828
import HodgeLean.Foundations.Program.G32PropFourSixPacked0829
import HodgeLean.Foundations.Program.G32PropFourSixPacked0830
import HodgeLean.Foundations.Program.G32PropFourSixPacked0831
import HodgeLean.Foundations.Program.G32PropFourSixPacked0832
import HodgeLean.Foundations.Program.G32PropFourSixPacked0833
import HodgeLean.Foundations.Program.G32PropFourSixPacked0834
import HodgeLean.Foundations.Program.G32PropFourSixPacked0822
import HodgeLean.Foundations.Program.G32PropFourSixPacked0823
import HodgeLean.Foundations.Program.G32PropFourSixPacked0824
import HodgeLean.Foundations.Program.G32PropFourSixPacked0825
import HodgeLean.Foundations.Program.G32PropFourSixPacked0820
import HodgeLean.Foundations.Program.G32PropFourSixPacked0821
import HodgeLean.Foundations.Program.G32PropFourSixPacked0815
import HodgeLean.Foundations.Program.G32PropFourSixPacked0816
import HodgeLean.Foundations.Program.G32PropFourSixPacked0817
import HodgeLean.Foundations.Program.G32PropFourSixPacked0814
import HodgeLean.Foundations.Program.G32PropFourSixPacked0818
import HodgeLean.Foundations.Program.G32PropFourSixPacked0826
import HodgeLean.Foundations.Program.G32PropFourSixPacked0827
import HodgeLean.Foundations.Program.G32PropFourSixPacked0819
import HodgeLean.Foundations.Program.G32PropFourSixSupplierRow31
import HodgeLean.Foundations.Program.G32PropFourSixArchiveReverse

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row31_cosetWordsPart0065 : Fin 8640 → List (Fin 4) :=
  fun i => (if i.val < 8384 then
(if i.val < 8352 then
(if i.val < 8336 then
(if i.val < 8328 then
(if i.val < 8324 then
(if i.val < 8322 then
(if i.val < 8321 then
[3, 0, 2, 2, 1, 0, 0, 3, 3, 2]
else
[3, 0, 2, 2, 3, 3, 0, 1, 2, 3])
else
(if i.val < 8323 then
[3, 0, 2, 3, 3, 0, 2, 3, 3, 2]
else
[3, 2, 1, 0, 3, 2, 2, 1, 1, 3]))
else
(if i.val < 8326 then
(if i.val < 8325 then
[3, 2, 1, 0, 3, 2, 2, 1, 3, 0]
else
[3, 2, 1, 1, 0, 2, 3, 0, 2, 1])
else
(if i.val < 8327 then
[3, 2, 1, 1, 0, 3, 3, 0, 2, 3]
else
[3, 2, 2, 1, 0, 3, 3, 0, 1, 2])))
else
(if i.val < 8332 then
(if i.val < 8330 then
(if i.val < 8329 then
[3, 2, 2, 1, 1, 3, 0, 1, 2, 1]
else
[3, 2, 2, 1, 3, 0, 0, 3, 2, 1])
else
(if i.val < 8331 then
[3, 2, 2, 1, 3, 0, 1, 2, 1, 1]
else
[3, 2, 2, 3, 0, 0, 3, 2, 1, 1]))
else
(if i.val < 8334 then
(if i.val < 8333 then
[3, 2, 2, 3, 0, 1, 2, 3, 3, 0]
else
[3, 3, 0, 0, 1, 2, 1, 1, 2, 3])
else
(if i.val < 8335 then
[3, 3, 0, 0, 1, 2, 2, 1, 3, 3]
else
[3, 3, 0, 0, 2, 1, 1, 2, 3, 0]))))
else
(if i.val < 8344 then
(if i.val < 8340 then
(if i.val < 8338 then
(if i.val < 8337 then
[3, 3, 0, 0, 2, 2, 1, 1, 3, 2]
else
[3, 3, 0, 1, 1, 0, 2, 1, 1, 2])
else
(if i.val < 8339 then
[3, 3, 0, 1, 1, 0, 3, 2, 1, 1]
else
[3, 3, 0, 1, 1, 0, 3, 2, 2, 1]))
else
(if i.val < 8342 then
(if i.val < 8341 then
[3, 3, 0, 1, 2, 1, 3, 2, 2, 1]
else
[3, 3, 0, 1, 2, 3, 0, 1, 1, 2])
else
(if i.val < 8343 then
[3, 3, 0, 2, 1, 0, 3, 2, 2, 1]
else
[3, 3, 0, 2, 1, 1, 2, 3, 0, 0])))
else
(if i.val < 8348 then
(if i.val < 8346 then
(if i.val < 8345 then
[3, 3, 0, 2, 1, 3, 3, 0, 1, 2]
else
[3, 3, 0, 2, 1, 3, 3, 2, 1, 0])
else
(if i.val < 8347 then
[3, 3, 0, 2, 3, 3, 2, 1, 0, 0]
else
[3, 3, 2, 1, 0, 0, 1, 3, 2, 2]))
else
(if i.val < 8350 then
(if i.val < 8349 then
[0, 0, 1, 0, 0, 1, 2, 2, 1, 3, 2]
else
[0, 0, 1, 0, 0, 2, 1, 1, 0, 2, 1])
else
(if i.val < 8351 then
[0, 0, 1, 0, 0, 2, 1, 1, 2, 3, 0]
else
[0, 0, 1, 0, 0, 2, 2, 1, 1, 3, 2])))))
else
(if i.val < 8368 then
(if i.val < 8360 then
(if i.val < 8356 then
(if i.val < 8354 then
(if i.val < 8353 then
[0, 0, 1, 0, 0, 2, 2, 1, 3, 0, 1]
else
[0, 0, 1, 0, 0, 3, 0, 0, 1, 1, 2])
else
(if i.val < 8355 then
[0, 0, 1, 0, 0, 3, 0, 1, 2, 2, 1]
else
[0, 0, 1, 0, 2, 2, 1, 3, 0, 0, 2]))
else
(if i.val < 8358 then
(if i.val < 8357 then
[0, 0, 1, 0, 2, 2, 1, 3, 2, 1, 1]
else
[0, 0, 1, 0, 2, 2, 3, 2, 2, 1, 3])
else
(if i.val < 8359 then
[0, 0, 1, 0, 2, 3, 0, 1, 1, 2, 3]
else
[0, 0, 1, 0, 2, 3, 0, 2, 1, 3, 2])))
else
(if i.val < 8364 then
(if i.val < 8362 then
(if i.val < 8361 then
[0, 0, 1, 0, 2, 3, 3, 0, 1, 1, 2]
else
[0, 0, 1, 0, 2, 3, 3, 0, 1, 2, 1])
else
(if i.val < 8363 then
[0, 0, 1, 0, 3, 0, 0, 1, 2, 3, 3]
else
[0, 0, 1, 0, 3, 2, 2, 1, 0, 3, 2]))
else
(if i.val < 8366 then
(if i.val < 8365 then
[0, 0, 1, 0, 3, 2, 2, 3, 0, 0, 3]
else
[0, 0, 1, 0, 3, 3, 0, 2, 3, 3, 2])
else
(if i.val < 8367 then
[0, 0, 1, 1, 0, 0, 2, 2, 3, 0, 1]
else
[0, 0, 1, 1, 0, 0, 2, 3, 0, 0, 3]))))
else
(if i.val < 8376 then
(if i.val < 8372 then
(if i.val < 8370 then
(if i.val < 8369 then
[0, 0, 1, 1, 0, 0, 3, 0, 1, 2, 1]
else
[0, 0, 1, 1, 0, 0, 3, 0, 1, 2, 2])
else
(if i.val < 8371 then
[0, 0, 1, 1, 0, 2, 1, 1, 0, 3, 2]
else
[0, 0, 1, 1, 0, 3, 0, 1, 2, 2, 1]))
else
(if i.val < 8374 then
(if i.val < 8373 then
[0, 0, 1, 1, 0, 3, 0, 1, 2, 3, 3]
else
[0, 0, 1, 1, 0, 3, 0, 2, 3, 3, 2])
else
(if i.val < 8375 then
[0, 0, 1, 1, 2, 1, 0, 0, 1, 3, 2]
else
[0, 0, 1, 1, 2, 1, 1, 0, 3, 2, 1])))
else
(if i.val < 8380 then
(if i.val < 8378 then
(if i.val < 8377 then
[0, 0, 1, 1, 2, 1, 1, 2, 3, 0, 1]
else
[0, 0, 1, 1, 2, 1, 1, 3, 2, 2, 1])
else
(if i.val < 8379 then
[0, 0, 1, 1, 2, 1, 3, 2, 2, 1, 3]
else
[0, 0, 1, 1, 2, 2, 1, 1, 3, 0, 0]))
else
(if i.val < 8382 then
(if i.val < 8381 then
[0, 0, 1, 1, 3, 0, 0, 2, 1, 1, 2]
else
[0, 0, 1, 1, 3, 0, 2, 1, 1, 3, 2])
else
(if i.val < 8383 then
[0, 0, 1, 1, 3, 0, 2, 3, 3, 0, 2]
else
[0, 0, 1, 1, 3, 0, 2, 3, 3, 2, 1]))))))
else
(if i.val < 8416 then
(if i.val < 8400 then
(if i.val < 8392 then
(if i.val < 8388 then
(if i.val < 8386 then
(if i.val < 8385 then
[0, 0, 1, 1, 3, 2, 1, 0, 3, 3, 2]
else
[0, 0, 1, 1, 3, 2, 1, 1, 2, 3, 3])
else
(if i.val < 8387 then
[0, 0, 1, 2, 1, 0, 0, 1, 2, 3, 0]
else
[0, 0, 1, 2, 1, 1, 0, 2, 1, 3, 0]))
else
(if i.val < 8390 then
(if i.val < 8389 then
[0, 0, 1, 2, 1, 1, 3, 0, 1, 1, 2]
else
[0, 0, 1, 2, 1, 1, 3, 0, 1, 2, 1])
else
(if i.val < 8391 then
[0, 0, 1, 2, 1, 1, 3, 0, 1, 2, 2]
else
[0, 0, 1, 2, 1, 1, 3, 2, 2, 3, 0])))
else
(if i.val < 8396 then
(if i.val < 8394 then
(if i.val < 8393 then
[0, 0, 1, 2, 1, 3, 0, 1, 2, 2, 3]
else
[0, 0, 1, 2, 1, 3, 3, 0, 1, 2, 1])
else
(if i.val < 8395 then
[0, 0, 1, 2, 2, 1, 0, 3, 0, 2, 1]
else
[0, 0, 1, 2, 2, 1, 0, 3, 0, 2, 3]))
else
(if i.val < 8398 then
(if i.val < 8397 then
[0, 0, 1, 2, 2, 1, 0, 3, 2, 1, 1]
else
[0, 0, 1, 2, 2, 1, 1, 0, 3, 2, 1])
else
(if i.val < 8399 then
[0, 0, 1, 2, 2, 1, 1, 3, 2, 1, 0]
else
[0, 0, 1, 2, 2, 1, 3, 0, 0, 2, 3]))))
else
(if i.val < 8408 then
(if i.val < 8404 then
(if i.val < 8402 then
(if i.val < 8401 then
[0, 0, 1, 2, 2, 3, 0, 2, 2, 1, 3]
else
[0, 0, 1, 2, 3, 0, 0, 1, 1, 2, 1])
else
(if i.val < 8403 then
[0, 0, 1, 2, 3, 0, 1, 1, 2, 1, 1]
else
[0, 0, 1, 2, 3, 0, 1, 2, 2, 1, 1]))
else
(if i.val < 8406 then
(if i.val < 8405 then
[0, 0, 1, 2, 3, 0, 1, 2, 2, 3, 0]
else
[0, 0, 1, 3, 0, 0, 1, 2, 3, 3, 2])
else
(if i.val < 8407 then
[0, 0, 1, 3, 0, 1, 2, 1, 0, 3, 2]
else
[0, 0, 1, 3, 0, 1, 2, 1, 1, 3, 3])))
else
(if i.val < 8412 then
(if i.val < 8410 then
(if i.val < 8409 then
[0, 0, 1, 3, 2, 1, 1, 0, 0, 2, 3]
else
[0, 0, 1, 3, 3, 0, 2, 1, 1, 2, 3])
else
(if i.val < 8411 then
[0, 0, 2, 1, 0, 3, 0, 2, 2, 1, 3]
else
[0, 0, 2, 1, 0, 3, 2, 1, 1, 0, 0]))
else
(if i.val < 8414 then
(if i.val < 8413 then
[0, 0, 2, 1, 1, 0, 2, 3, 0, 0, 3]
else
[0, 0, 2, 1, 1, 3, 0, 2, 3, 3, 2])
else
(if i.val < 8415 then
[0, 0, 2, 1, 1, 3, 2, 2, 1, 0, 0]
else
[0, 0, 2, 1, 3, 0, 1, 2, 1, 3, 0])))))
else
(if i.val < 8432 then
(if i.val < 8424 then
(if i.val < 8420 then
(if i.val < 8418 then
(if i.val < 8417 then
[0, 0, 2, 1, 3, 0, 1, 2, 2, 1, 0]
else
[0, 0, 2, 1, 3, 3, 0, 2, 1, 1, 2])
else
(if i.val < 8419 then
[0, 0, 2, 2, 1, 0, 0, 1, 2, 3, 3]
else
[0, 0, 2, 2, 1, 0, 3, 0, 0, 2, 1]))
else
(if i.val < 8422 then
(if i.val < 8421 then
[0, 0, 2, 2, 1, 1, 0, 3, 2, 1, 0]
else
[0, 0, 2, 2, 1, 3, 0, 1, 2, 3, 3])
else
(if i.val < 8423 then
[0, 0, 2, 2, 1, 3, 3, 0, 0, 2, 3]
else
[0, 0, 2, 2, 3, 0, 0, 3, 2, 1, 0])))
else
(if i.val < 8428 then
(if i.val < 8426 then
(if i.val < 8425 then
[0, 0, 2, 2, 3, 0, 1, 1, 0, 3, 2]
else
[0, 0, 2, 2, 3, 0, 2, 2, 1, 0, 3])
else
(if i.val < 8427 then
[0, 0, 2, 2, 3, 2, 1, 0, 3, 2, 2]
else
[0, 0, 2, 3, 0, 0, 1, 1, 2, 1, 3]))
else
(if i.val < 8430 then
(if i.val < 8429 then
[0, 0, 2, 3, 0, 1, 2, 1, 1, 0, 3]
else
[0, 0, 2, 3, 0, 1, 2, 1, 3, 2, 2])
else
(if i.val < 8431 then
[0, 0, 2, 3, 0, 1, 2, 2, 1, 3, 3]
else
[0, 0, 2, 3, 0, 1, 2, 2, 3, 0, 0]))))
else
(if i.val < 8440 then
(if i.val < 8436 then
(if i.val < 8434 then
(if i.val < 8433 then
[0, 0, 2, 3, 0, 1, 2, 2, 3, 3, 0]
else
[0, 0, 2, 3, 2, 1, 0, 3, 2, 2, 1])
else
(if i.val < 8435 then
[0, 0, 2, 3, 2, 1, 1, 0, 3, 2, 1]
else
[0, 0, 2, 3, 2, 2, 1, 3, 0, 1, 2]))
else
(if i.val < 8438 then
(if i.val < 8437 then
[0, 0, 2, 3, 3, 0, 1, 2, 1, 1, 0]
else
[0, 0, 3, 0, 0, 2, 2, 3, 2, 2, 1])
else
(if i.val < 8439 then
[0, 0, 3, 0, 0, 2, 3, 3, 2, 1, 0]
else
[0, 0, 3, 0, 1, 2, 1, 1, 0, 2, 3])))
else
(if i.val < 8444 then
(if i.val < 8442 then
(if i.val < 8441 then
[0, 0, 3, 0, 1, 2, 2, 1, 1, 3, 2]
else
[0, 0, 3, 0, 1, 2, 3, 3, 2, 1, 1])
else
(if i.val < 8443 then
[0, 0, 3, 0, 2, 1, 0, 3, 2, 2, 3]
else
[0, 0, 3, 0, 2, 1, 1, 0, 2, 3, 2]))
else
(if i.val < 8446 then
(if i.val < 8445 then
[0, 0, 3, 0, 2, 1, 1, 0, 3, 3, 2]
else
[0, 0, 3, 0, 2, 1, 1, 3, 2, 2, 3])
else
(if i.val < 8447 then
[0, 0, 3, 0, 2, 3, 3, 2, 1, 0, 0]
else
[0, 0, 3, 2, 1, 0, 3, 2, 2, 1, 0])))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row31_cosetWordsPart0066 : Fin 8640 → List (Fin 4) :=
  fun i => (if i.val < 8512 then
(if i.val < 8480 then
(if i.val < 8464 then
(if i.val < 8456 then
(if i.val < 8452 then
(if i.val < 8450 then
(if i.val < 8449 then
[0, 0, 3, 2, 1, 0, 3, 2, 2, 1, 3]
else
[0, 0, 3, 2, 1, 1, 2, 3, 3, 2, 1])
else
(if i.val < 8451 then
[0, 0, 3, 2, 2, 1, 3, 0, 1, 2, 1]
else
[0, 0, 3, 2, 2, 1, 3, 0, 1, 2, 3]))
else
(if i.val < 8454 then
(if i.val < 8453 then
[0, 0, 3, 2, 2, 3, 0, 1, 2, 3, 3]
else
[0, 0, 3, 3, 0, 0, 2, 2, 1, 0, 0])
else
(if i.val < 8455 then
[0, 0, 3, 3, 0, 2, 3, 3, 2, 1, 1]
else
[0, 0, 3, 3, 2, 1, 0, 3, 3, 0, 1])))
else
(if i.val < 8460 then
(if i.val < 8458 then
(if i.val < 8457 then
[0, 0, 3, 3, 2, 1, 1, 0, 3, 3, 2]
else
[0, 0, 3, 3, 2, 2, 1, 1, 0, 3, 3])
else
(if i.val < 8459 then
[0, 1, 0, 0, 1, 2, 1, 1, 2, 3, 3]
else
[0, 1, 0, 0, 1, 2, 1, 1, 3, 3, 2]))
else
(if i.val < 8462 then
(if i.val < 8461 then
[0, 1, 0, 0, 1, 2, 2, 1, 0, 3, 3]
else
[0, 1, 0, 0, 2, 1, 1, 2, 3, 0, 0])
else
(if i.val < 8463 then
[0, 1, 0, 0, 2, 1, 3, 3, 0, 1, 2]
else
[0, 1, 0, 0, 2, 2, 1, 3, 0, 1, 1]))))
else
(if i.val < 8472 then
(if i.val < 8468 then
(if i.val < 8466 then
(if i.val < 8465 then
[0, 1, 0, 0, 2, 2, 3, 2, 2, 1, 3]
else
[0, 1, 0, 0, 2, 3, 2, 2, 1, 1, 0])
else
(if i.val < 8467 then
[0, 1, 0, 0, 2, 3, 2, 2, 1, 1, 3]
else
[0, 1, 0, 0, 2, 3, 3, 0, 1, 2, 3]))
else
(if i.val < 8470 then
(if i.val < 8469 then
[0, 1, 0, 0, 3, 3, 0, 1, 2, 2, 3]
else
[0, 1, 0, 0, 3, 3, 0, 2, 2, 1, 0])
else
(if i.val < 8471 then
[0, 1, 0, 2, 1, 1, 0, 2, 3, 0, 0]
else
[0, 1, 0, 2, 1, 1, 2, 3, 3, 0, 0])))
else
(if i.val < 8476 then
(if i.val < 8474 then
(if i.val < 8473 then
[0, 1, 0, 2, 1, 3, 3, 0, 1, 2, 3]
else
[0, 1, 0, 2, 2, 1, 1, 0, 3, 2, 1])
else
(if i.val < 8475 then
[0, 1, 0, 2, 2, 3, 0, 0, 1, 1, 2]
else
[0, 1, 0, 2, 2, 3, 0, 2, 2, 1, 3]))
else
(if i.val < 8478 then
(if i.val < 8477 then
[0, 1, 0, 2, 2, 3, 2, 2, 1, 0, 3]
else
[0, 1, 0, 2, 3, 0, 1, 1, 2, 1, 1])
else
(if i.val < 8479 then
[0, 1, 0, 2, 3, 3, 0, 1, 2, 1, 1]
else
[0, 1, 0, 2, 3, 3, 0, 1, 2, 1, 3])))))
else
(if i.val < 8496 then
(if i.val < 8488 then
(if i.val < 8484 then
(if i.val < 8482 then
(if i.val < 8481 then
[0, 1, 0, 2, 3, 3, 0, 1, 2, 3, 3]
else
[0, 1, 0, 3, 0, 0, 1, 1, 2, 2, 1])
else
(if i.val < 8483 then
[0, 1, 0, 3, 0, 0, 1, 1, 2, 3, 3]
else
[0, 1, 0, 3, 0, 0, 1, 2, 3, 3, 2]))
else
(if i.val < 8486 then
(if i.val < 8485 then
[0, 1, 0, 3, 2, 2, 1, 0, 3, 2, 1]
else
[0, 1, 0, 3, 3, 0, 0, 2, 3, 3, 2])
else
(if i.val < 8487 then
[0, 1, 0, 3, 3, 2, 1, 0, 3, 2, 2]
else
[0, 1, 1, 0, 0, 2, 1, 1, 2, 3, 0])))
else
(if i.val < 8492 then
(if i.val < 8490 then
(if i.val < 8489 then
[0, 1, 1, 0, 0, 3, 0, 1, 2, 3, 3]
else
[0, 1, 1, 0, 2, 1, 0, 0, 1, 3, 2])
else
(if i.val < 8491 then
[0, 1, 1, 0, 2, 1, 1, 0, 2, 1, 3]
else
[0, 1, 1, 0, 2, 1, 1, 0, 2, 3, 0]))
else
(if i.val < 8494 then
(if i.val < 8493 then
[0, 1, 1, 0, 2, 1, 1, 2, 3, 0, 0]
else
[0, 1, 1, 0, 2, 1, 3, 3, 2, 2, 1])
else
(if i.val < 8495 then
[0, 1, 1, 0, 3, 2, 1, 1, 0, 0, 2]
else
[0, 1, 1, 0, 3, 2, 1, 1, 2, 3, 0]))))
else
(if i.val < 8504 then
(if i.val < 8500 then
(if i.val < 8498 then
(if i.val < 8497 then
[0, 1, 1, 2, 1, 1, 0, 3, 0, 2, 1]
else
[0, 1, 1, 2, 1, 1, 2, 3, 3, 0, 1])
else
(if i.val < 8499 then
[0, 1, 1, 2, 1, 3, 3, 2, 2, 1, 1]
else
[0, 1, 1, 2, 3, 0, 1, 1, 2, 1, 0]))
else
(if i.val < 8502 then
(if i.val < 8501 then
[0, 1, 1, 2, 3, 0, 1, 1, 2, 1, 1]
else
[0, 1, 1, 2, 3, 0, 1, 1, 2, 3, 3])
else
(if i.val < 8503 then
[0, 1, 1, 2, 3, 0, 1, 2, 1, 3, 2]
else
[0, 1, 1, 2, 3, 0, 1, 2, 2, 1, 3])))
else
(if i.val < 8508 then
(if i.val < 8506 then
(if i.val < 8505 then
[0, 1, 1, 2, 3, 2, 2, 1, 3, 2, 2]
else
[0, 1, 1, 3, 0, 0, 1, 1, 2, 3, 3])
else
(if i.val < 8507 then
[0, 1, 1, 3, 0, 2, 3, 3, 2, 1, 1]
else
[0, 1, 1, 3, 2, 2, 1, 0, 3, 2, 1]))
else
(if i.val < 8510 then
(if i.val < 8509 then
[0, 1, 1, 3, 2, 2, 1, 1, 3, 0, 1]
else
[0, 1, 2, 1, 0, 0, 1, 3, 2, 2, 3])
else
(if i.val < 8511 then
[0, 1, 2, 1, 1, 0, 0, 3, 2, 2, 1]
else
[0, 1, 2, 1, 1, 3, 0, 1, 2, 2, 3]))))))
else
(if i.val < 8544 then
(if i.val < 8528 then
(if i.val < 8520 then
(if i.val < 8516 then
(if i.val < 8514 then
(if i.val < 8513 then
[0, 1, 2, 1, 1, 3, 2, 2, 1, 1, 3]
else
[0, 1, 2, 1, 3, 0, 0, 3, 2, 2, 1])
else
(if i.val < 8515 then
[0, 1, 2, 1, 3, 0, 1, 2, 2, 3, 0]
else
[0, 1, 2, 1, 3, 3, 0, 1, 2, 1, 1]))
else
(if i.val < 8518 then
(if i.val < 8517 then
[0, 1, 2, 2, 1, 0, 0, 1, 2, 3, 3]
else
[0, 1, 2, 2, 1, 0, 3, 0, 2, 3, 3])
else
(if i.val < 8519 then
[0, 1, 2, 2, 1, 1, 0, 3, 0, 2, 1]
else
[0, 1, 2, 2, 1, 3, 0, 0, 1, 2, 3])))
else
(if i.val < 8524 then
(if i.val < 8522 then
(if i.val < 8521 then
[0, 1, 2, 2, 1, 3, 3, 2, 1, 0, 3]
else
[0, 1, 2, 2, 3, 0, 2, 2, 1, 0, 3])
else
(if i.val < 8523 then
[0, 1, 2, 3, 0, 0, 1, 1, 2, 1, 1]
else
[0, 1, 2, 3, 0, 0, 3, 2, 2, 1, 3]))
else
(if i.val < 8526 then
(if i.val < 8525 then
[0, 1, 2, 3, 0, 0, 3, 2, 2, 3, 0]
else
[0, 1, 2, 3, 2, 2, 1, 0, 3, 2, 2])
else
(if i.val < 8527 then
[0, 1, 2, 3, 3, 0, 0, 1, 1, 2, 2]
else
[0, 1, 2, 3, 3, 0, 1, 2, 1, 1, 0]))))
else
(if i.val < 8536 then
(if i.val < 8532 then
(if i.val < 8530 then
(if i.val < 8529 then
[0, 1, 2, 3, 3, 0, 1, 2, 1, 1, 3]
else
[0, 1, 2, 3, 3, 0, 1, 2, 1, 3, 3])
else
(if i.val < 8531 then
[0, 1, 2, 3, 3, 0, 1, 2, 3, 0, 0]
else
[0, 1, 3, 0, 0, 1, 1, 2, 1, 0, 0]))
else
(if i.val < 8534 then
(if i.val < 8533 then
[0, 1, 3, 0, 0, 1, 1, 2, 2, 1, 0]
else
[0, 1, 3, 0, 0, 1, 1, 2, 2, 1, 1])
else
(if i.val < 8535 then
[0, 1, 3, 0, 0, 1, 1, 2, 3, 3, 2]
else
[0, 1, 3, 2, 2, 1, 1, 3, 0, 2, 1])))
else
(if i.val < 8540 then
(if i.val < 8538 then
(if i.val < 8537 then
[0, 1, 3, 3, 0, 0, 1, 2, 3, 3, 2]
else
[0, 1, 3, 3, 0, 0, 2, 3, 3, 2, 1])
else
(if i.val < 8539 then
[0, 2, 1, 0, 3, 3, 0, 0, 2, 3, 3]
else
[0, 2, 1, 1, 0, 0, 3, 3, 0, 2, 2]))
else
(if i.val < 8542 then
(if i.val < 8541 then
[0, 2, 1, 1, 0, 3, 0, 2, 1, 0, 0]
else
[0, 2, 1, 1, 0, 3, 2, 1, 1, 2, 3])
else
(if i.val < 8543 then
[0, 2, 1, 1, 2, 3, 0, 1, 2, 2, 1]
else
[0, 2, 1, 1, 3, 0, 0, 2, 1, 1, 2])))))
else
(if i.val < 8560 then
(if i.val < 8552 then
(if i.val < 8548 then
(if i.val < 8546 then
(if i.val < 8545 then
[0, 2, 1, 1, 3, 2, 2, 1, 0, 3, 2]
else
[0, 2, 1, 3, 3, 0, 0, 2, 3, 3, 2])
else
(if i.val < 8547 then
[0, 2, 2, 1, 0, 3, 3, 0, 1, 2, 3]
else
[0, 2, 2, 1, 1, 0, 3, 0, 2, 1, 0]))
else
(if i.val < 8550 then
(if i.val < 8549 then
[0, 2, 2, 1, 3, 3, 0, 1, 2, 1, 0]
else
[0, 2, 2, 3, 2, 1, 0, 0, 1, 2, 2])
else
(if i.val < 8551 then
[0, 2, 2, 3, 2, 2, 3, 0, 0, 3, 2]
else
[0, 2, 2, 3, 3, 0, 1, 2, 1, 1, 0])))
else
(if i.val < 8556 then
(if i.val < 8554 then
(if i.val < 8553 then
[0, 2, 2, 3, 3, 0, 2, 3, 3, 2, 1]
else
[0, 2, 3, 0, 1, 1, 0, 2, 1, 0, 0])
else
(if i.val < 8555 then
[0, 2, 3, 0, 1, 1, 0, 2, 1, 1, 2]
else
[0, 2, 3, 0, 1, 2, 1, 3, 3, 2, 2]))
else
(if i.val < 8558 then
(if i.val < 8557 then
[0, 2, 3, 0, 1, 2, 2, 3, 3, 0, 0]
else
[0, 2, 3, 0, 2, 1, 1, 0, 0, 2, 1])
else
(if i.val < 8559 then
[0, 2, 3, 0, 2, 1, 1, 0, 3, 0, 2]
else
[0, 2, 3, 0, 2, 1, 1, 3, 2, 2, 3]))))
else
(if i.val < 8568 then
(if i.val < 8564 then
(if i.val < 8562 then
(if i.val < 8561 then
[0, 2, 3, 0, 2, 1, 3, 3, 2, 2, 1]
else
[0, 2, 3, 2, 1, 1, 0, 2, 3, 2, 1])
else
(if i.val < 8563 then
[0, 2, 3, 2, 2, 1, 3, 0, 1, 2, 3]
else
[0, 2, 3, 3, 0, 1, 1, 0, 2, 2, 1]))
else
(if i.val < 8566 then
(if i.val < 8565 then
[0, 2, 3, 3, 0, 2, 3, 3, 2, 1, 1]
else
[0, 2, 3, 3, 2, 1, 1, 0, 3, 3, 2])
else
(if i.val < 8567 then
[0, 3, 0, 0, 1, 1, 2, 1, 3, 3, 0]
else
[0, 3, 0, 0, 1, 1, 2, 2, 3, 0, 1])))
else
(if i.val < 8572 then
(if i.val < 8570 then
(if i.val < 8569 then
[0, 3, 0, 0, 1, 2, 3, 3, 2, 1, 1]
else
[0, 3, 0, 0, 3, 2, 1, 0, 3, 2, 2])
else
(if i.val < 8571 then
[0, 3, 0, 0, 3, 2, 2, 3, 0, 1, 2]
else
[0, 3, 0, 1, 1, 2, 1, 1, 2, 3, 3]))
else
(if i.val < 8574 then
(if i.val < 8573 then
[0, 3, 0, 2, 1, 0, 0, 1, 2, 2, 3]
else
[0, 3, 0, 2, 1, 1, 0, 2, 1, 1, 2])
else
(if i.val < 8575 then
[0, 3, 0, 2, 1, 3, 3, 0, 2, 2, 3]
else
[0, 3, 0, 2, 2, 3, 3, 0, 1, 2, 3])))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row31_cosetWordsPart0067 : Fin 8640 → List (Fin 4) :=
  fun i => (if i.val < 8608 then
(if i.val < 8592 then
(if i.val < 8584 then
(if i.val < 8580 then
(if i.val < 8578 then
(if i.val < 8577 then
[0, 3, 2, 1, 1, 0, 2, 3, 0, 2, 1]
else
[0, 3, 2, 2, 1, 3, 0, 0, 3, 2, 1])
else
(if i.val < 8579 then
[0, 3, 2, 2, 1, 3, 0, 1, 2, 1, 1]
else
[0, 3, 3, 0, 1, 1, 0, 3, 2, 2, 1]))
else
(if i.val < 8582 then
(if i.val < 8581 then
[0, 3, 3, 0, 2, 1, 3, 3, 2, 1, 0]
else
[0, 3, 3, 0, 2, 3, 3, 2, 1, 0, 0])
else
(if i.val < 8583 then
[1, 0, 0, 1, 2, 2, 3, 0, 0, 3, 2]
else
[1, 0, 0, 1, 3, 3, 2, 1, 1, 2, 3])))
else
(if i.val < 8588 then
(if i.val < 8586 then
(if i.val < 8585 then
[1, 0, 0, 2, 1, 3, 2, 1, 1, 2, 3]
else
[1, 0, 0, 2, 2, 3, 2, 2, 1, 1, 3])
else
(if i.val < 8587 then
[1, 0, 0, 2, 3, 0, 2, 2, 3, 3, 0]
else
[1, 0, 0, 2, 3, 3, 2, 2, 1, 1, 0]))
else
(if i.val < 8590 then
(if i.val < 8589 then
[1, 0, 0, 3, 3, 0, 2, 1, 0, 3, 3]
else
[1, 0, 0, 3, 3, 2, 1, 1, 0, 3, 3])
else
(if i.val < 8591 then
[1, 0, 2, 1, 1, 0, 3, 3, 0, 2, 2]
else
[1, 0, 2, 1, 1, 3, 0, 0, 1, 2, 1]))))
else
(if i.val < 8600 then
(if i.val < 8596 then
(if i.val < 8594 then
(if i.val < 8593 then
[1, 0, 2, 2, 1, 3, 3, 2, 1, 0, 3]
else
[1, 0, 2, 2, 3, 0, 0, 3, 2, 1, 0])
else
(if i.val < 8595 then
[1, 0, 2, 2, 3, 3, 0, 2, 3, 3, 2]
else
[1, 0, 2, 3, 0, 0, 3, 2, 2, 3, 0]))
else
(if i.val < 8598 then
(if i.val < 8597 then
[1, 0, 2, 3, 0, 1, 1, 2, 3, 0, 1]
else
[1, 0, 2, 3, 3, 0, 1, 1, 0, 2, 3])
else
(if i.val < 8599 then
[1, 0, 2, 3, 3, 0, 2, 1, 1, 3, 2]
else
[1, 0, 3, 0, 2, 1, 1, 0, 2, 3, 2])))
else
(if i.val < 8604 then
(if i.val < 8602 then
(if i.val < 8601 then
[1, 0, 3, 0, 2, 2, 1, 0, 3, 0, 1]
else
[1, 1, 0, 0, 2, 3, 0, 1, 2, 2, 3])
else
(if i.val < 8603 then
[1, 1, 0, 0, 3, 0, 2, 3, 3, 2, 1]
else
[1, 1, 0, 2, 2, 1, 1, 3, 2, 2, 3]))
else
(if i.val < 8606 then
(if i.val < 8605 then
[1, 1, 0, 2, 2, 3, 0, 1, 2, 3, 3]
else
[1, 1, 0, 2, 2, 3, 2, 2, 3, 0, 0])
else
(if i.val < 8607 then
[1, 1, 0, 3, 0, 0, 1, 1, 2, 1, 3]
else
[1, 1, 0, 3, 0, 0, 1, 1, 2, 2, 3])))))
else
(if i.val < 8624 then
(if i.val < 8616 then
(if i.val < 8612 then
(if i.val < 8610 then
(if i.val < 8609 then
[1, 1, 2, 1, 1, 0, 2, 3, 0, 2, 1]
else
[1, 1, 2, 1, 1, 3, 0, 2, 1, 1, 2])
else
(if i.val < 8611 then
[1, 1, 2, 3, 0, 1, 1, 0, 2, 3, 2]
else
[1, 1, 2, 3, 0, 2, 1, 1, 3, 2, 2]))
else
(if i.val < 8614 then
(if i.val < 8613 then
[1, 1, 3, 0, 0, 1, 1, 2, 1, 0, 0]
else
[1, 1, 3, 0, 2, 3, 3, 0, 2, 1, 1])
else
(if i.val < 8615 then
[1, 2, 1, 0, 3, 3, 0, 2, 3, 3, 2]
else
[1, 2, 1, 3, 0, 1, 2, 2, 3, 0, 0])))
else
(if i.val < 8620 then
(if i.val < 8618 then
(if i.val < 8617 then
[1, 2, 2, 1, 0, 3, 0, 2, 3, 3, 0]
else
[1, 2, 3, 0, 1, 2, 2, 3, 3, 0, 0])
else
(if i.val < 8619 then
[1, 2, 3, 3, 0, 0, 2, 1, 1, 2, 3]
else
[1, 3, 0, 1, 2, 2, 1, 3, 0, 1, 2]))
else
(if i.val < 8622 then
(if i.val < 8621 then
[1, 3, 0, 2, 3, 3, 0, 2, 3, 3, 2]
else
[2, 1, 0, 3, 0, 0, 1, 1, 2, 3, 3])
else
(if i.val < 8623 then
[2, 1, 1, 0, 0, 3, 0, 1, 2, 3, 3]
else
[2, 1, 1, 0, 2, 3, 2, 1, 1, 0, 0]))))
else
(if i.val < 8632 then
(if i.val < 8628 then
(if i.val < 8626 then
(if i.val < 8625 then
[2, 1, 1, 3, 0, 2, 3, 3, 0, 2, 1]
else
[2, 2, 3, 0, 1, 1, 0, 2, 1, 1, 2])
else
(if i.val < 8627 then
[2, 2, 3, 0, 1, 2, 1, 1, 0, 2, 3]
else
[2, 3, 0, 1, 1, 0, 3, 2, 1, 1, 2]))
else
(if i.val < 8630 then
(if i.val < 8629 then
[2, 3, 0, 2, 2, 1, 0, 0, 3, 3, 2]
else
[2, 3, 3, 0, 2, 1, 3, 3, 0, 1, 2])
else
(if i.val < 8631 then
[0, 0, 1, 0, 0, 2, 1, 1, 2, 3, 0, 0]
else
[0, 0, 1, 0, 3, 0, 0, 1, 1, 2, 3, 3])))
else
(if i.val < 8636 then
(if i.val < 8634 then
(if i.val < 8633 then
[0, 0, 1, 0, 3, 2, 2, 1, 0, 3, 2, 1]
else
[0, 0, 1, 1, 2, 1, 1, 0, 3, 0, 2, 1])
else
(if i.val < 8635 then
[0, 0, 1, 2, 1, 3, 0, 1, 2, 2, 3, 0]
else
[0, 0, 1, 2, 2, 3, 0, 2, 2, 1, 0, 3]))
else
(if i.val < 8638 then
(if i.val < 8637 then
[0, 0, 2, 3, 2, 2, 1, 3, 0, 1, 2, 3]
else
[0, 0, 3, 2, 2, 1, 3, 0, 1, 2, 1, 1])
else
(if i.val < 8639 then
[0, 1, 0, 2, 2, 1, 3, 3, 2, 1, 0, 3]
else
[0, 2, 2, 3, 0, 1, 1, 0, 2, 1, 1, 2]))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row31_cosetRepresentatives : Fin 8640 → HurwitzPrymRex_Mat :=
  fun i => (if i.val < 4352 then
(if i.val < 2176 then
(if i.val < 1024 then
(if i.val < 512 then
(if i.val < 256 then
(if i.val < 128 then
g32p_row31_cosetRepresentativesPart0000 i
else
g32p_row31_cosetRepresentativesPart0001 i)
else
(if i.val < 384 then
g32p_row31_cosetRepresentativesPart0002 i
else
g32p_row31_cosetRepresentativesPart0003 i))
else
(if i.val < 768 then
(if i.val < 640 then
g32p_row31_cosetRepresentativesPart0004 i
else
g32p_row31_cosetRepresentativesPart0005 i)
else
(if i.val < 896 then
g32p_row31_cosetRepresentativesPart0006 i
else
g32p_row31_cosetRepresentativesPart0007 i)))
else
(if i.val < 1536 then
(if i.val < 1280 then
(if i.val < 1152 then
g32p_row31_cosetRepresentativesPart0008 i
else
g32p_row31_cosetRepresentativesPart0009 i)
else
(if i.val < 1408 then
g32p_row31_cosetRepresentativesPart0010 i
else
g32p_row31_cosetRepresentativesPart0011 i))
else
(if i.val < 1792 then
(if i.val < 1664 then
g32p_row31_cosetRepresentativesPart0012 i
else
g32p_row31_cosetRepresentativesPart0013 i)
else
(if i.val < 1920 then
g32p_row31_cosetRepresentativesPart0014 i
else
(if i.val < 2048 then
g32p_row31_cosetRepresentativesPart0015 i
else
g32p_row31_cosetRepresentativesPart0016 i)))))
else
(if i.val < 3200 then
(if i.val < 2688 then
(if i.val < 2432 then
(if i.val < 2304 then
g32p_row31_cosetRepresentativesPart0017 i
else
g32p_row31_cosetRepresentativesPart0018 i)
else
(if i.val < 2560 then
g32p_row31_cosetRepresentativesPart0019 i
else
g32p_row31_cosetRepresentativesPart0020 i))
else
(if i.val < 2944 then
(if i.val < 2816 then
g32p_row31_cosetRepresentativesPart0021 i
else
g32p_row31_cosetRepresentativesPart0022 i)
else
(if i.val < 3072 then
g32p_row31_cosetRepresentativesPart0023 i
else
g32p_row31_cosetRepresentativesPart0024 i)))
else
(if i.val < 3712 then
(if i.val < 3456 then
(if i.val < 3328 then
g32p_row31_cosetRepresentativesPart0025 i
else
g32p_row31_cosetRepresentativesPart0026 i)
else
(if i.val < 3584 then
g32p_row31_cosetRepresentativesPart0027 i
else
g32p_row31_cosetRepresentativesPart0028 i))
else
(if i.val < 3968 then
(if i.val < 3840 then
g32p_row31_cosetRepresentativesPart0029 i
else
g32p_row31_cosetRepresentativesPart0030 i)
else
(if i.val < 4096 then
g32p_row31_cosetRepresentativesPart0031 i
else
(if i.val < 4224 then
g32p_row31_cosetRepresentativesPart0032 i
else
g32p_row31_cosetRepresentativesPart0033 i))))))
else
(if i.val < 6528 then
(if i.val < 5376 then
(if i.val < 4864 then
(if i.val < 4608 then
(if i.val < 4480 then
g32p_row31_cosetRepresentativesPart0034 i
else
g32p_row31_cosetRepresentativesPart0035 i)
else
(if i.val < 4736 then
g32p_row31_cosetRepresentativesPart0036 i
else
g32p_row31_cosetRepresentativesPart0037 i))
else
(if i.val < 5120 then
(if i.val < 4992 then
g32p_row31_cosetRepresentativesPart0038 i
else
g32p_row31_cosetRepresentativesPart0039 i)
else
(if i.val < 5248 then
g32p_row31_cosetRepresentativesPart0040 i
else
g32p_row31_cosetRepresentativesPart0041 i)))
else
(if i.val < 5888 then
(if i.val < 5632 then
(if i.val < 5504 then
g32p_row31_cosetRepresentativesPart0042 i
else
g32p_row31_cosetRepresentativesPart0043 i)
else
(if i.val < 5760 then
g32p_row31_cosetRepresentativesPart0044 i
else
g32p_row31_cosetRepresentativesPart0045 i))
else
(if i.val < 6144 then
(if i.val < 6016 then
g32p_row31_cosetRepresentativesPart0046 i
else
g32p_row31_cosetRepresentativesPart0047 i)
else
(if i.val < 6272 then
g32p_row31_cosetRepresentativesPart0048 i
else
(if i.val < 6400 then
g32p_row31_cosetRepresentativesPart0049 i
else
g32p_row31_cosetRepresentativesPart0050 i)))))
else
(if i.val < 7552 then
(if i.val < 7040 then
(if i.val < 6784 then
(if i.val < 6656 then
g32p_row31_cosetRepresentativesPart0051 i
else
g32p_row31_cosetRepresentativesPart0052 i)
else
(if i.val < 6912 then
g32p_row31_cosetRepresentativesPart0053 i
else
g32p_row31_cosetRepresentativesPart0054 i))
else
(if i.val < 7296 then
(if i.val < 7168 then
g32p_row31_cosetRepresentativesPart0055 i
else
g32p_row31_cosetRepresentativesPart0056 i)
else
(if i.val < 7424 then
g32p_row31_cosetRepresentativesPart0057 i
else
g32p_row31_cosetRepresentativesPart0058 i)))
else
(if i.val < 8064 then
(if i.val < 7808 then
(if i.val < 7680 then
g32p_row31_cosetRepresentativesPart0059 i
else
g32p_row31_cosetRepresentativesPart0060 i)
else
(if i.val < 7936 then
g32p_row31_cosetRepresentativesPart0061 i
else
g32p_row31_cosetRepresentativesPart0062 i))
else
(if i.val < 8320 then
(if i.val < 8192 then
g32p_row31_cosetRepresentativesPart0063 i
else
g32p_row31_cosetRepresentativesPart0064 i)
else
(if i.val < 8448 then
g32p_row31_cosetRepresentativesPart0065 i
else
(if i.val < 8576 then
g32p_row31_cosetRepresentativesPart0066 i
else
g32p_row31_cosetRepresentativesPart0067 i)))))))

def g32p_row31_cosetWords : Fin 8640 → List (Fin 4) :=
  fun i => (if i.val < 4352 then
(if i.val < 2176 then
(if i.val < 1024 then
(if i.val < 512 then
(if i.val < 256 then
(if i.val < 128 then
g32p_row31_cosetWordsPart0000 i
else
g32p_row31_cosetWordsPart0001 i)
else
(if i.val < 384 then
g32p_row31_cosetWordsPart0002 i
else
g32p_row31_cosetWordsPart0003 i))
else
(if i.val < 768 then
(if i.val < 640 then
g32p_row31_cosetWordsPart0004 i
else
g32p_row31_cosetWordsPart0005 i)
else
(if i.val < 896 then
g32p_row31_cosetWordsPart0006 i
else
g32p_row31_cosetWordsPart0007 i)))
else
(if i.val < 1536 then
(if i.val < 1280 then
(if i.val < 1152 then
g32p_row31_cosetWordsPart0008 i
else
g32p_row31_cosetWordsPart0009 i)
else
(if i.val < 1408 then
g32p_row31_cosetWordsPart0010 i
else
g32p_row31_cosetWordsPart0011 i))
else
(if i.val < 1792 then
(if i.val < 1664 then
g32p_row31_cosetWordsPart0012 i
else
g32p_row31_cosetWordsPart0013 i)
else
(if i.val < 1920 then
g32p_row31_cosetWordsPart0014 i
else
(if i.val < 2048 then
g32p_row31_cosetWordsPart0015 i
else
g32p_row31_cosetWordsPart0016 i)))))
else
(if i.val < 3200 then
(if i.val < 2688 then
(if i.val < 2432 then
(if i.val < 2304 then
g32p_row31_cosetWordsPart0017 i
else
g32p_row31_cosetWordsPart0018 i)
else
(if i.val < 2560 then
g32p_row31_cosetWordsPart0019 i
else
g32p_row31_cosetWordsPart0020 i))
else
(if i.val < 2944 then
(if i.val < 2816 then
g32p_row31_cosetWordsPart0021 i
else
g32p_row31_cosetWordsPart0022 i)
else
(if i.val < 3072 then
g32p_row31_cosetWordsPart0023 i
else
g32p_row31_cosetWordsPart0024 i)))
else
(if i.val < 3712 then
(if i.val < 3456 then
(if i.val < 3328 then
g32p_row31_cosetWordsPart0025 i
else
g32p_row31_cosetWordsPart0026 i)
else
(if i.val < 3584 then
g32p_row31_cosetWordsPart0027 i
else
g32p_row31_cosetWordsPart0028 i))
else
(if i.val < 3968 then
(if i.val < 3840 then
g32p_row31_cosetWordsPart0029 i
else
g32p_row31_cosetWordsPart0030 i)
else
(if i.val < 4096 then
g32p_row31_cosetWordsPart0031 i
else
(if i.val < 4224 then
g32p_row31_cosetWordsPart0032 i
else
g32p_row31_cosetWordsPart0033 i))))))
else
(if i.val < 6528 then
(if i.val < 5376 then
(if i.val < 4864 then
(if i.val < 4608 then
(if i.val < 4480 then
g32p_row31_cosetWordsPart0034 i
else
g32p_row31_cosetWordsPart0035 i)
else
(if i.val < 4736 then
g32p_row31_cosetWordsPart0036 i
else
g32p_row31_cosetWordsPart0037 i))
else
(if i.val < 5120 then
(if i.val < 4992 then
g32p_row31_cosetWordsPart0038 i
else
g32p_row31_cosetWordsPart0039 i)
else
(if i.val < 5248 then
g32p_row31_cosetWordsPart0040 i
else
g32p_row31_cosetWordsPart0041 i)))
else
(if i.val < 5888 then
(if i.val < 5632 then
(if i.val < 5504 then
g32p_row31_cosetWordsPart0042 i
else
g32p_row31_cosetWordsPart0043 i)
else
(if i.val < 5760 then
g32p_row31_cosetWordsPart0044 i
else
g32p_row31_cosetWordsPart0045 i))
else
(if i.val < 6144 then
(if i.val < 6016 then
g32p_row31_cosetWordsPart0046 i
else
g32p_row31_cosetWordsPart0047 i)
else
(if i.val < 6272 then
g32p_row31_cosetWordsPart0048 i
else
(if i.val < 6400 then
g32p_row31_cosetWordsPart0049 i
else
g32p_row31_cosetWordsPart0050 i)))))
else
(if i.val < 7552 then
(if i.val < 7040 then
(if i.val < 6784 then
(if i.val < 6656 then
g32p_row31_cosetWordsPart0051 i
else
g32p_row31_cosetWordsPart0052 i)
else
(if i.val < 6912 then
g32p_row31_cosetWordsPart0053 i
else
g32p_row31_cosetWordsPart0054 i))
else
(if i.val < 7296 then
(if i.val < 7168 then
g32p_row31_cosetWordsPart0055 i
else
g32p_row31_cosetWordsPart0056 i)
else
(if i.val < 7424 then
g32p_row31_cosetWordsPart0057 i
else
g32p_row31_cosetWordsPart0058 i)))
else
(if i.val < 8064 then
(if i.val < 7808 then
(if i.val < 7680 then
g32p_row31_cosetWordsPart0059 i
else
g32p_row31_cosetWordsPart0060 i)
else
(if i.val < 7936 then
g32p_row31_cosetWordsPart0061 i
else
g32p_row31_cosetWordsPart0062 i))
else
(if i.val < 8320 then
(if i.val < 8192 then
g32p_row31_cosetWordsPart0063 i
else
g32p_row31_cosetWordsPart0064 i)
else
(if i.val < 8448 then
g32p_row31_cosetWordsPart0065 i
else
(if i.val < 8576 then
g32p_row31_cosetWordsPart0066 i
else
g32p_row31_cosetWordsPart0067 i)))))))

def g32p_row31_cosetBranchMatrices : Fin 3 → HurwitzPrymRex_Mat :=
  ![![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]], ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, -2⟩, ⟨0, -2⟩, ⟨-1, -2⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩]], ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩]]]

def g32p_row31_cosetGeneratorNextColumn0 : Fin 8640 → Fin 8640 :=
  fun i => (if i.val < 4096 then
(if i.val < 2048 then
(if i.val < 1024 then
(if i.val < 512 then
g32p_row31_cosetGeneratorNextColumn0Part0000 i
else
g32p_row31_cosetGeneratorNextColumn0Part0001 i)
else
(if i.val < 1536 then
g32p_row31_cosetGeneratorNextColumn0Part0002 i
else
g32p_row31_cosetGeneratorNextColumn0Part0003 i))
else
(if i.val < 3072 then
(if i.val < 2560 then
g32p_row31_cosetGeneratorNextColumn0Part0004 i
else
g32p_row31_cosetGeneratorNextColumn0Part0005 i)
else
(if i.val < 3584 then
g32p_row31_cosetGeneratorNextColumn0Part0006 i
else
g32p_row31_cosetGeneratorNextColumn0Part0007 i)))
else
(if i.val < 6144 then
(if i.val < 5120 then
(if i.val < 4608 then
g32p_row31_cosetGeneratorNextColumn0Part0008 i
else
g32p_row31_cosetGeneratorNextColumn0Part0009 i)
else
(if i.val < 5632 then
g32p_row31_cosetGeneratorNextColumn0Part0010 i
else
g32p_row31_cosetGeneratorNextColumn0Part0011 i))
else
(if i.val < 7168 then
(if i.val < 6656 then
g32p_row31_cosetGeneratorNextColumn0Part0012 i
else
g32p_row31_cosetGeneratorNextColumn0Part0013 i)
else
(if i.val < 7680 then
g32p_row31_cosetGeneratorNextColumn0Part0014 i
else
(if i.val < 8192 then
g32p_row31_cosetGeneratorNextColumn0Part0015 i
else
g32p_row31_cosetGeneratorNextColumn0Part0016 i)))))

def g32p_row31_cosetGeneratorNextColumn1 : Fin 8640 → Fin 8640 :=
  fun i => (if i.val < 4096 then
(if i.val < 2048 then
(if i.val < 1024 then
(if i.val < 512 then
g32p_row31_cosetGeneratorNextColumn1Part0000 i
else
g32p_row31_cosetGeneratorNextColumn1Part0001 i)
else
(if i.val < 1536 then
g32p_row31_cosetGeneratorNextColumn1Part0002 i
else
g32p_row31_cosetGeneratorNextColumn1Part0003 i))
else
(if i.val < 3072 then
(if i.val < 2560 then
g32p_row31_cosetGeneratorNextColumn1Part0004 i
else
g32p_row31_cosetGeneratorNextColumn1Part0005 i)
else
(if i.val < 3584 then
g32p_row31_cosetGeneratorNextColumn1Part0006 i
else
g32p_row31_cosetGeneratorNextColumn1Part0007 i)))
else
(if i.val < 6144 then
(if i.val < 5120 then
(if i.val < 4608 then
g32p_row31_cosetGeneratorNextColumn1Part0008 i
else
g32p_row31_cosetGeneratorNextColumn1Part0009 i)
else
(if i.val < 5632 then
g32p_row31_cosetGeneratorNextColumn1Part0010 i
else
g32p_row31_cosetGeneratorNextColumn1Part0011 i))
else
(if i.val < 7168 then
(if i.val < 6656 then
g32p_row31_cosetGeneratorNextColumn1Part0012 i
else
g32p_row31_cosetGeneratorNextColumn1Part0013 i)
else
(if i.val < 7680 then
g32p_row31_cosetGeneratorNextColumn1Part0014 i
else
(if i.val < 8192 then
g32p_row31_cosetGeneratorNextColumn1Part0015 i
else
g32p_row31_cosetGeneratorNextColumn1Part0016 i)))))

def g32p_row31_cosetGeneratorNextColumn2 : Fin 8640 → Fin 8640 :=
  fun i => (if i.val < 4096 then
(if i.val < 2048 then
(if i.val < 1024 then
(if i.val < 512 then
g32p_row31_cosetGeneratorNextColumn2Part0000 i
else
g32p_row31_cosetGeneratorNextColumn2Part0001 i)
else
(if i.val < 1536 then
g32p_row31_cosetGeneratorNextColumn2Part0002 i
else
g32p_row31_cosetGeneratorNextColumn2Part0003 i))
else
(if i.val < 3072 then
(if i.val < 2560 then
g32p_row31_cosetGeneratorNextColumn2Part0004 i
else
g32p_row31_cosetGeneratorNextColumn2Part0005 i)
else
(if i.val < 3584 then
g32p_row31_cosetGeneratorNextColumn2Part0006 i
else
g32p_row31_cosetGeneratorNextColumn2Part0007 i)))
else
(if i.val < 6144 then
(if i.val < 5120 then
(if i.val < 4608 then
g32p_row31_cosetGeneratorNextColumn2Part0008 i
else
g32p_row31_cosetGeneratorNextColumn2Part0009 i)
else
(if i.val < 5632 then
g32p_row31_cosetGeneratorNextColumn2Part0010 i
else
g32p_row31_cosetGeneratorNextColumn2Part0011 i))
else
(if i.val < 7168 then
(if i.val < 6656 then
g32p_row31_cosetGeneratorNextColumn2Part0012 i
else
g32p_row31_cosetGeneratorNextColumn2Part0013 i)
else
(if i.val < 7680 then
g32p_row31_cosetGeneratorNextColumn2Part0014 i
else
(if i.val < 8192 then
g32p_row31_cosetGeneratorNextColumn2Part0015 i
else
g32p_row31_cosetGeneratorNextColumn2Part0016 i)))))

def g32p_row31_cosetGeneratorNextColumn3 : Fin 8640 → Fin 8640 :=
  fun i => (if i.val < 4096 then
(if i.val < 2048 then
(if i.val < 1024 then
(if i.val < 512 then
g32p_row31_cosetGeneratorNextColumn3Part0000 i
else
g32p_row31_cosetGeneratorNextColumn3Part0001 i)
else
(if i.val < 1536 then
g32p_row31_cosetGeneratorNextColumn3Part0002 i
else
g32p_row31_cosetGeneratorNextColumn3Part0003 i))
else
(if i.val < 3072 then
(if i.val < 2560 then
g32p_row31_cosetGeneratorNextColumn3Part0004 i
else
g32p_row31_cosetGeneratorNextColumn3Part0005 i)
else
(if i.val < 3584 then
g32p_row31_cosetGeneratorNextColumn3Part0006 i
else
g32p_row31_cosetGeneratorNextColumn3Part0007 i)))
else
(if i.val < 6144 then
(if i.val < 5120 then
(if i.val < 4608 then
g32p_row31_cosetGeneratorNextColumn3Part0008 i
else
g32p_row31_cosetGeneratorNextColumn3Part0009 i)
else
(if i.val < 5632 then
g32p_row31_cosetGeneratorNextColumn3Part0010 i
else
g32p_row31_cosetGeneratorNextColumn3Part0011 i))
else
(if i.val < 7168 then
(if i.val < 6656 then
g32p_row31_cosetGeneratorNextColumn3Part0012 i
else
g32p_row31_cosetGeneratorNextColumn3Part0013 i)
else
(if i.val < 7680 then
g32p_row31_cosetGeneratorNextColumn3Part0014 i
else
(if i.val < 8192 then
g32p_row31_cosetGeneratorNextColumn3Part0015 i
else
g32p_row31_cosetGeneratorNextColumn3Part0016 i)))))

def g32p_row31_cosetGeneratorNext : Fin 4 → Fin 8640 → Fin 8640 :=
  ![g32p_row31_cosetGeneratorNextColumn0, g32p_row31_cosetGeneratorNextColumn1, g32p_row31_cosetGeneratorNextColumn2, g32p_row31_cosetGeneratorNextColumn3]

def g32p_row31_cosetGeneratorFactorColumn0 : Fin 8640 → Fin 18 :=
  fun i => (if i.val < 4096 then
(if i.val < 2048 then
(if i.val < 1024 then
(if i.val < 512 then
g32p_row31_cosetGeneratorFactorColumn0Part0000 i
else
g32p_row31_cosetGeneratorFactorColumn0Part0001 i)
else
(if i.val < 1536 then
g32p_row31_cosetGeneratorFactorColumn0Part0002 i
else
g32p_row31_cosetGeneratorFactorColumn0Part0003 i))
else
(if i.val < 3072 then
(if i.val < 2560 then
g32p_row31_cosetGeneratorFactorColumn0Part0004 i
else
g32p_row31_cosetGeneratorFactorColumn0Part0005 i)
else
(if i.val < 3584 then
g32p_row31_cosetGeneratorFactorColumn0Part0006 i
else
g32p_row31_cosetGeneratorFactorColumn0Part0007 i)))
else
(if i.val < 6144 then
(if i.val < 5120 then
(if i.val < 4608 then
g32p_row31_cosetGeneratorFactorColumn0Part0008 i
else
g32p_row31_cosetGeneratorFactorColumn0Part0009 i)
else
(if i.val < 5632 then
g32p_row31_cosetGeneratorFactorColumn0Part0010 i
else
g32p_row31_cosetGeneratorFactorColumn0Part0011 i))
else
(if i.val < 7168 then
(if i.val < 6656 then
g32p_row31_cosetGeneratorFactorColumn0Part0012 i
else
g32p_row31_cosetGeneratorFactorColumn0Part0013 i)
else
(if i.val < 7680 then
g32p_row31_cosetGeneratorFactorColumn0Part0014 i
else
(if i.val < 8192 then
g32p_row31_cosetGeneratorFactorColumn0Part0015 i
else
g32p_row31_cosetGeneratorFactorColumn0Part0016 i)))))

def g32p_row31_cosetGeneratorFactorColumn1 : Fin 8640 → Fin 18 :=
  fun i => (if i.val < 4096 then
(if i.val < 2048 then
(if i.val < 1024 then
(if i.val < 512 then
g32p_row31_cosetGeneratorFactorColumn1Part0000 i
else
g32p_row31_cosetGeneratorFactorColumn1Part0001 i)
else
(if i.val < 1536 then
g32p_row31_cosetGeneratorFactorColumn1Part0002 i
else
g32p_row31_cosetGeneratorFactorColumn1Part0003 i))
else
(if i.val < 3072 then
(if i.val < 2560 then
g32p_row31_cosetGeneratorFactorColumn1Part0004 i
else
g32p_row31_cosetGeneratorFactorColumn1Part0005 i)
else
(if i.val < 3584 then
g32p_row31_cosetGeneratorFactorColumn1Part0006 i
else
g32p_row31_cosetGeneratorFactorColumn1Part0007 i)))
else
(if i.val < 6144 then
(if i.val < 5120 then
(if i.val < 4608 then
g32p_row31_cosetGeneratorFactorColumn1Part0008 i
else
g32p_row31_cosetGeneratorFactorColumn1Part0009 i)
else
(if i.val < 5632 then
g32p_row31_cosetGeneratorFactorColumn1Part0010 i
else
g32p_row31_cosetGeneratorFactorColumn1Part0011 i))
else
(if i.val < 7168 then
(if i.val < 6656 then
g32p_row31_cosetGeneratorFactorColumn1Part0012 i
else
g32p_row31_cosetGeneratorFactorColumn1Part0013 i)
else
(if i.val < 7680 then
g32p_row31_cosetGeneratorFactorColumn1Part0014 i
else
(if i.val < 8192 then
g32p_row31_cosetGeneratorFactorColumn1Part0015 i
else
g32p_row31_cosetGeneratorFactorColumn1Part0016 i)))))

def g32p_row31_cosetGeneratorFactorColumn2 : Fin 8640 → Fin 18 :=
  fun i => (if i.val < 4096 then
(if i.val < 2048 then
(if i.val < 1024 then
(if i.val < 512 then
g32p_row31_cosetGeneratorFactorColumn2Part0000 i
else
g32p_row31_cosetGeneratorFactorColumn2Part0001 i)
else
(if i.val < 1536 then
g32p_row31_cosetGeneratorFactorColumn2Part0002 i
else
g32p_row31_cosetGeneratorFactorColumn2Part0003 i))
else
(if i.val < 3072 then
(if i.val < 2560 then
g32p_row31_cosetGeneratorFactorColumn2Part0004 i
else
g32p_row31_cosetGeneratorFactorColumn2Part0005 i)
else
(if i.val < 3584 then
g32p_row31_cosetGeneratorFactorColumn2Part0006 i
else
g32p_row31_cosetGeneratorFactorColumn2Part0007 i)))
else
(if i.val < 6144 then
(if i.val < 5120 then
(if i.val < 4608 then
g32p_row31_cosetGeneratorFactorColumn2Part0008 i
else
g32p_row31_cosetGeneratorFactorColumn2Part0009 i)
else
(if i.val < 5632 then
g32p_row31_cosetGeneratorFactorColumn2Part0010 i
else
g32p_row31_cosetGeneratorFactorColumn2Part0011 i))
else
(if i.val < 7168 then
(if i.val < 6656 then
g32p_row31_cosetGeneratorFactorColumn2Part0012 i
else
g32p_row31_cosetGeneratorFactorColumn2Part0013 i)
else
(if i.val < 7680 then
g32p_row31_cosetGeneratorFactorColumn2Part0014 i
else
(if i.val < 8192 then
g32p_row31_cosetGeneratorFactorColumn2Part0015 i
else
g32p_row31_cosetGeneratorFactorColumn2Part0016 i)))))

def g32p_row31_cosetGeneratorFactorColumn3 : Fin 8640 → Fin 18 :=
  fun i => (if i.val < 4096 then
(if i.val < 2048 then
(if i.val < 1024 then
(if i.val < 512 then
g32p_row31_cosetGeneratorFactorColumn3Part0000 i
else
g32p_row31_cosetGeneratorFactorColumn3Part0001 i)
else
(if i.val < 1536 then
g32p_row31_cosetGeneratorFactorColumn3Part0002 i
else
g32p_row31_cosetGeneratorFactorColumn3Part0003 i))
else
(if i.val < 3072 then
(if i.val < 2560 then
g32p_row31_cosetGeneratorFactorColumn3Part0004 i
else
g32p_row31_cosetGeneratorFactorColumn3Part0005 i)
else
(if i.val < 3584 then
g32p_row31_cosetGeneratorFactorColumn3Part0006 i
else
g32p_row31_cosetGeneratorFactorColumn3Part0007 i)))
else
(if i.val < 6144 then
(if i.val < 5120 then
(if i.val < 4608 then
g32p_row31_cosetGeneratorFactorColumn3Part0008 i
else
g32p_row31_cosetGeneratorFactorColumn3Part0009 i)
else
(if i.val < 5632 then
g32p_row31_cosetGeneratorFactorColumn3Part0010 i
else
g32p_row31_cosetGeneratorFactorColumn3Part0011 i))
else
(if i.val < 7168 then
(if i.val < 6656 then
g32p_row31_cosetGeneratorFactorColumn3Part0012 i
else
g32p_row31_cosetGeneratorFactorColumn3Part0013 i)
else
(if i.val < 7680 then
g32p_row31_cosetGeneratorFactorColumn3Part0014 i
else
(if i.val < 8192 then
g32p_row31_cosetGeneratorFactorColumn3Part0015 i
else
g32p_row31_cosetGeneratorFactorColumn3Part0016 i)))))

def g32p_row31_cosetGeneratorFactor : Fin 4 → Fin 8640 → Fin 18 :=
  ![g32p_row31_cosetGeneratorFactorColumn0, g32p_row31_cosetGeneratorFactorColumn1, g32p_row31_cosetGeneratorFactorColumn2, g32p_row31_cosetGeneratorFactorColumn3]

def g32p_row31_cosetBranchNextColumn0 : Fin 8640 → Fin 8640 :=
  fun i => (if i.val < 4096 then
(if i.val < 2048 then
(if i.val < 1024 then
(if i.val < 512 then
g32p_row31_cosetBranchNextColumn0Part0000 i
else
g32p_row31_cosetBranchNextColumn0Part0001 i)
else
(if i.val < 1536 then
g32p_row31_cosetBranchNextColumn0Part0002 i
else
g32p_row31_cosetBranchNextColumn0Part0003 i))
else
(if i.val < 3072 then
(if i.val < 2560 then
g32p_row31_cosetBranchNextColumn0Part0004 i
else
g32p_row31_cosetBranchNextColumn0Part0005 i)
else
(if i.val < 3584 then
g32p_row31_cosetBranchNextColumn0Part0006 i
else
g32p_row31_cosetBranchNextColumn0Part0007 i)))
else
(if i.val < 6144 then
(if i.val < 5120 then
(if i.val < 4608 then
g32p_row31_cosetBranchNextColumn0Part0008 i
else
g32p_row31_cosetBranchNextColumn0Part0009 i)
else
(if i.val < 5632 then
g32p_row31_cosetBranchNextColumn0Part0010 i
else
g32p_row31_cosetBranchNextColumn0Part0011 i))
else
(if i.val < 7168 then
(if i.val < 6656 then
g32p_row31_cosetBranchNextColumn0Part0012 i
else
g32p_row31_cosetBranchNextColumn0Part0013 i)
else
(if i.val < 7680 then
g32p_row31_cosetBranchNextColumn0Part0014 i
else
(if i.val < 8192 then
g32p_row31_cosetBranchNextColumn0Part0015 i
else
g32p_row31_cosetBranchNextColumn0Part0016 i)))))

def g32p_row31_cosetBranchNextColumn1 : Fin 8640 → Fin 8640 :=
  fun i => (if i.val < 4096 then
(if i.val < 2048 then
(if i.val < 1024 then
(if i.val < 512 then
g32p_row31_cosetBranchNextColumn1Part0000 i
else
g32p_row31_cosetBranchNextColumn1Part0001 i)
else
(if i.val < 1536 then
g32p_row31_cosetBranchNextColumn1Part0002 i
else
g32p_row31_cosetBranchNextColumn1Part0003 i))
else
(if i.val < 3072 then
(if i.val < 2560 then
g32p_row31_cosetBranchNextColumn1Part0004 i
else
g32p_row31_cosetBranchNextColumn1Part0005 i)
else
(if i.val < 3584 then
g32p_row31_cosetBranchNextColumn1Part0006 i
else
g32p_row31_cosetBranchNextColumn1Part0007 i)))
else
(if i.val < 6144 then
(if i.val < 5120 then
(if i.val < 4608 then
g32p_row31_cosetBranchNextColumn1Part0008 i
else
g32p_row31_cosetBranchNextColumn1Part0009 i)
else
(if i.val < 5632 then
g32p_row31_cosetBranchNextColumn1Part0010 i
else
g32p_row31_cosetBranchNextColumn1Part0011 i))
else
(if i.val < 7168 then
(if i.val < 6656 then
g32p_row31_cosetBranchNextColumn1Part0012 i
else
g32p_row31_cosetBranchNextColumn1Part0013 i)
else
(if i.val < 7680 then
g32p_row31_cosetBranchNextColumn1Part0014 i
else
(if i.val < 8192 then
g32p_row31_cosetBranchNextColumn1Part0015 i
else
g32p_row31_cosetBranchNextColumn1Part0016 i)))))

def g32p_row31_cosetBranchNextColumn2 : Fin 8640 → Fin 8640 :=
  fun i => (if i.val < 4096 then
(if i.val < 2048 then
(if i.val < 1024 then
(if i.val < 512 then
g32p_row31_cosetBranchNextColumn2Part0000 i
else
g32p_row31_cosetBranchNextColumn2Part0001 i)
else
(if i.val < 1536 then
g32p_row31_cosetBranchNextColumn2Part0002 i
else
g32p_row31_cosetBranchNextColumn2Part0003 i))
else
(if i.val < 3072 then
(if i.val < 2560 then
g32p_row31_cosetBranchNextColumn2Part0004 i
else
g32p_row31_cosetBranchNextColumn2Part0005 i)
else
(if i.val < 3584 then
g32p_row31_cosetBranchNextColumn2Part0006 i
else
g32p_row31_cosetBranchNextColumn2Part0007 i)))
else
(if i.val < 6144 then
(if i.val < 5120 then
(if i.val < 4608 then
g32p_row31_cosetBranchNextColumn2Part0008 i
else
g32p_row31_cosetBranchNextColumn2Part0009 i)
else
(if i.val < 5632 then
g32p_row31_cosetBranchNextColumn2Part0010 i
else
g32p_row31_cosetBranchNextColumn2Part0011 i))
else
(if i.val < 7168 then
(if i.val < 6656 then
g32p_row31_cosetBranchNextColumn2Part0012 i
else
g32p_row31_cosetBranchNextColumn2Part0013 i)
else
(if i.val < 7680 then
g32p_row31_cosetBranchNextColumn2Part0014 i
else
(if i.val < 8192 then
g32p_row31_cosetBranchNextColumn2Part0015 i
else
g32p_row31_cosetBranchNextColumn2Part0016 i)))))

def g32p_row31_cosetBranchNext : Fin 3 → Fin 8640 → Fin 8640 :=
  ![g32p_row31_cosetBranchNextColumn0, g32p_row31_cosetBranchNextColumn1, g32p_row31_cosetBranchNextColumn2]

def g32p_row31_cosetBranchFactorColumn0 : Fin 8640 → Fin 18 :=
  fun i => (if i.val < 4096 then
(if i.val < 2048 then
(if i.val < 1024 then
(if i.val < 512 then
g32p_row31_cosetBranchFactorColumn0Part0000 i
else
g32p_row31_cosetBranchFactorColumn0Part0001 i)
else
(if i.val < 1536 then
g32p_row31_cosetBranchFactorColumn0Part0002 i
else
g32p_row31_cosetBranchFactorColumn0Part0003 i))
else
(if i.val < 3072 then
(if i.val < 2560 then
g32p_row31_cosetBranchFactorColumn0Part0004 i
else
g32p_row31_cosetBranchFactorColumn0Part0005 i)
else
(if i.val < 3584 then
g32p_row31_cosetBranchFactorColumn0Part0006 i
else
g32p_row31_cosetBranchFactorColumn0Part0007 i)))
else
(if i.val < 6144 then
(if i.val < 5120 then
(if i.val < 4608 then
g32p_row31_cosetBranchFactorColumn0Part0008 i
else
g32p_row31_cosetBranchFactorColumn0Part0009 i)
else
(if i.val < 5632 then
g32p_row31_cosetBranchFactorColumn0Part0010 i
else
g32p_row31_cosetBranchFactorColumn0Part0011 i))
else
(if i.val < 7168 then
(if i.val < 6656 then
g32p_row31_cosetBranchFactorColumn0Part0012 i
else
g32p_row31_cosetBranchFactorColumn0Part0013 i)
else
(if i.val < 7680 then
g32p_row31_cosetBranchFactorColumn0Part0014 i
else
(if i.val < 8192 then
g32p_row31_cosetBranchFactorColumn0Part0015 i
else
g32p_row31_cosetBranchFactorColumn0Part0016 i)))))

def g32p_row31_cosetBranchFactorColumn1 : Fin 8640 → Fin 18 :=
  fun i => (if i.val < 4096 then
(if i.val < 2048 then
(if i.val < 1024 then
(if i.val < 512 then
g32p_row31_cosetBranchFactorColumn1Part0000 i
else
g32p_row31_cosetBranchFactorColumn1Part0001 i)
else
(if i.val < 1536 then
g32p_row31_cosetBranchFactorColumn1Part0002 i
else
g32p_row31_cosetBranchFactorColumn1Part0003 i))
else
(if i.val < 3072 then
(if i.val < 2560 then
g32p_row31_cosetBranchFactorColumn1Part0004 i
else
g32p_row31_cosetBranchFactorColumn1Part0005 i)
else
(if i.val < 3584 then
g32p_row31_cosetBranchFactorColumn1Part0006 i
else
g32p_row31_cosetBranchFactorColumn1Part0007 i)))
else
(if i.val < 6144 then
(if i.val < 5120 then
(if i.val < 4608 then
g32p_row31_cosetBranchFactorColumn1Part0008 i
else
g32p_row31_cosetBranchFactorColumn1Part0009 i)
else
(if i.val < 5632 then
g32p_row31_cosetBranchFactorColumn1Part0010 i
else
g32p_row31_cosetBranchFactorColumn1Part0011 i))
else
(if i.val < 7168 then
(if i.val < 6656 then
g32p_row31_cosetBranchFactorColumn1Part0012 i
else
g32p_row31_cosetBranchFactorColumn1Part0013 i)
else
(if i.val < 7680 then
g32p_row31_cosetBranchFactorColumn1Part0014 i
else
(if i.val < 8192 then
g32p_row31_cosetBranchFactorColumn1Part0015 i
else
g32p_row31_cosetBranchFactorColumn1Part0016 i)))))

def g32p_row31_cosetBranchFactorColumn2 : Fin 8640 → Fin 18 :=
  fun i => (if i.val < 4096 then
(if i.val < 2048 then
(if i.val < 1024 then
(if i.val < 512 then
g32p_row31_cosetBranchFactorColumn2Part0000 i
else
g32p_row31_cosetBranchFactorColumn2Part0001 i)
else
(if i.val < 1536 then
g32p_row31_cosetBranchFactorColumn2Part0002 i
else
g32p_row31_cosetBranchFactorColumn2Part0003 i))
else
(if i.val < 3072 then
(if i.val < 2560 then
g32p_row31_cosetBranchFactorColumn2Part0004 i
else
g32p_row31_cosetBranchFactorColumn2Part0005 i)
else
(if i.val < 3584 then
g32p_row31_cosetBranchFactorColumn2Part0006 i
else
g32p_row31_cosetBranchFactorColumn2Part0007 i)))
else
(if i.val < 6144 then
(if i.val < 5120 then
(if i.val < 4608 then
g32p_row31_cosetBranchFactorColumn2Part0008 i
else
g32p_row31_cosetBranchFactorColumn2Part0009 i)
else
(if i.val < 5632 then
g32p_row31_cosetBranchFactorColumn2Part0010 i
else
g32p_row31_cosetBranchFactorColumn2Part0011 i))
else
(if i.val < 7168 then
(if i.val < 6656 then
g32p_row31_cosetBranchFactorColumn2Part0012 i
else
g32p_row31_cosetBranchFactorColumn2Part0013 i)
else
(if i.val < 7680 then
g32p_row31_cosetBranchFactorColumn2Part0014 i
else
(if i.val < 8192 then
g32p_row31_cosetBranchFactorColumn2Part0015 i
else
g32p_row31_cosetBranchFactorColumn2Part0016 i)))))

def g32p_row31_cosetBranchFactor : Fin 3 → Fin 8640 → Fin 18 :=
  ![g32p_row31_cosetBranchFactorColumn0, g32p_row31_cosetBranchFactorColumn1, g32p_row31_cosetBranchFactorColumn2]

def g32p_row31_cosetLabels0 : Fin 8640 → Fin 2880 :=
  fun i => (if i.val < 4096 then
(if i.val < 2048 then
(if i.val < 1024 then
(if i.val < 512 then
g32p_row31_cosetLabels0Part0000 i
else
g32p_row31_cosetLabels0Part0001 i)
else
(if i.val < 1536 then
g32p_row31_cosetLabels0Part0002 i
else
g32p_row31_cosetLabels0Part0003 i))
else
(if i.val < 3072 then
(if i.val < 2560 then
g32p_row31_cosetLabels0Part0004 i
else
g32p_row31_cosetLabels0Part0005 i)
else
(if i.val < 3584 then
g32p_row31_cosetLabels0Part0006 i
else
g32p_row31_cosetLabels0Part0007 i)))
else
(if i.val < 6144 then
(if i.val < 5120 then
(if i.val < 4608 then
g32p_row31_cosetLabels0Part0008 i
else
g32p_row31_cosetLabels0Part0009 i)
else
(if i.val < 5632 then
g32p_row31_cosetLabels0Part0010 i
else
g32p_row31_cosetLabels0Part0011 i))
else
(if i.val < 7168 then
(if i.val < 6656 then
g32p_row31_cosetLabels0Part0012 i
else
g32p_row31_cosetLabels0Part0013 i)
else
(if i.val < 7680 then
g32p_row31_cosetLabels0Part0014 i
else
(if i.val < 8192 then
g32p_row31_cosetLabels0Part0015 i
else
g32p_row31_cosetLabels0Part0016 i)))))

def g32p_row31_cosetDistances0 : Fin 8640 → ℕ :=
  fun i => (if i.val < 4096 then
(if i.val < 2048 then
(if i.val < 1024 then
(if i.val < 512 then
g32p_row31_cosetDistances0Part0000 i
else
g32p_row31_cosetDistances0Part0001 i)
else
(if i.val < 1536 then
g32p_row31_cosetDistances0Part0002 i
else
g32p_row31_cosetDistances0Part0003 i))
else
(if i.val < 3072 then
(if i.val < 2560 then
g32p_row31_cosetDistances0Part0004 i
else
g32p_row31_cosetDistances0Part0005 i)
else
(if i.val < 3584 then
g32p_row31_cosetDistances0Part0006 i
else
g32p_row31_cosetDistances0Part0007 i)))
else
(if i.val < 6144 then
(if i.val < 5120 then
(if i.val < 4608 then
g32p_row31_cosetDistances0Part0008 i
else
g32p_row31_cosetDistances0Part0009 i)
else
(if i.val < 5632 then
g32p_row31_cosetDistances0Part0010 i
else
g32p_row31_cosetDistances0Part0011 i))
else
(if i.val < 7168 then
(if i.val < 6656 then
g32p_row31_cosetDistances0Part0012 i
else
g32p_row31_cosetDistances0Part0013 i)
else
(if i.val < 7680 then
g32p_row31_cosetDistances0Part0014 i
else
(if i.val < 8192 then
g32p_row31_cosetDistances0Part0015 i
else
g32p_row31_cosetDistances0Part0016 i)))))

def g32p_row31_cosetRoots0 : Fin 2880 → Fin 8640 :=
  fun i => (if i.val < 1536 then
(if i.val < 512 then
g32p_row31_cosetRoots0Part0000 i
else
(if i.val < 1024 then
g32p_row31_cosetRoots0Part0001 i
else
g32p_row31_cosetRoots0Part0002 i))
else
(if i.val < 2048 then
g32p_row31_cosetRoots0Part0003 i
else
(if i.val < 2560 then
g32p_row31_cosetRoots0Part0004 i
else
g32p_row31_cosetRoots0Part0005 i)))

def g32p_row31_cosetLengths0 : Fin 2880 → ℕ :=
  fun i => (if i.val < 1536 then
(if i.val < 512 then
g32p_row31_cosetLengths0Part0000 i
else
(if i.val < 1024 then
g32p_row31_cosetLengths0Part0001 i
else
g32p_row31_cosetLengths0Part0002 i))
else
(if i.val < 2048 then
g32p_row31_cosetLengths0Part0003 i
else
(if i.val < 2560 then
g32p_row31_cosetLengths0Part0004 i
else
g32p_row31_cosetLengths0Part0005 i)))

def g32p_row31_cosetCycleNodes0 : Fin 2880 → List ℕ :=
  fun i => (if i.val < 1536 then
(if i.val < 512 then
g32p_row31_cosetCycleNodes0Part0000 i
else
(if i.val < 1024 then
g32p_row31_cosetCycleNodes0Part0001 i
else
g32p_row31_cosetCycleNodes0Part0002 i))
else
(if i.val < 2048 then
g32p_row31_cosetCycleNodes0Part0003 i
else
(if i.val < 2560 then
g32p_row31_cosetCycleNodes0Part0004 i
else
g32p_row31_cosetCycleNodes0Part0005 i)))

def g32p_row31_cosetCycles0 : List (List ℕ) :=
  List.ofFn g32p_row31_cosetCycleNodes0

def g32p_row31_cosetMonodromies0 : Fin 2880 → Fin 18 :=
  fun i => (if i.val < 1536 then
(if i.val < 512 then
g32p_row31_cosetMonodromies0Part0000 i
else
(if i.val < 1024 then
g32p_row31_cosetMonodromies0Part0001 i
else
g32p_row31_cosetMonodromies0Part0002 i))
else
(if i.val < 2048 then
g32p_row31_cosetMonodromies0Part0003 i
else
(if i.val < 2560 then
g32p_row31_cosetMonodromies0Part0004 i
else
g32p_row31_cosetMonodromies0Part0005 i)))

def g32p_row31_cosetExponents0 : Fin 2880 → Multiplicative (ZMod 6) :=
  fun i => (if i.val < 1536 then
(if i.val < 512 then
g32p_row31_cosetExponents0Part0000 i
else
(if i.val < 1024 then
g32p_row31_cosetExponents0Part0001 i
else
g32p_row31_cosetExponents0Part0002 i))
else
(if i.val < 2048 then
g32p_row31_cosetExponents0Part0003 i
else
(if i.val < 2560 then
g32p_row31_cosetExponents0Part0004 i
else
g32p_row31_cosetExponents0Part0005 i)))

def g32p_row31_cosetLabels1 : Fin 8640 → Fin 2880 :=
  fun i => (if i.val < 4096 then
(if i.val < 2048 then
(if i.val < 1024 then
(if i.val < 512 then
g32p_row31_cosetLabels1Part0000 i
else
g32p_row31_cosetLabels1Part0001 i)
else
(if i.val < 1536 then
g32p_row31_cosetLabels1Part0002 i
else
g32p_row31_cosetLabels1Part0003 i))
else
(if i.val < 3072 then
(if i.val < 2560 then
g32p_row31_cosetLabels1Part0004 i
else
g32p_row31_cosetLabels1Part0005 i)
else
(if i.val < 3584 then
g32p_row31_cosetLabels1Part0006 i
else
g32p_row31_cosetLabels1Part0007 i)))
else
(if i.val < 6144 then
(if i.val < 5120 then
(if i.val < 4608 then
g32p_row31_cosetLabels1Part0008 i
else
g32p_row31_cosetLabels1Part0009 i)
else
(if i.val < 5632 then
g32p_row31_cosetLabels1Part0010 i
else
g32p_row31_cosetLabels1Part0011 i))
else
(if i.val < 7168 then
(if i.val < 6656 then
g32p_row31_cosetLabels1Part0012 i
else
g32p_row31_cosetLabels1Part0013 i)
else
(if i.val < 7680 then
g32p_row31_cosetLabels1Part0014 i
else
(if i.val < 8192 then
g32p_row31_cosetLabels1Part0015 i
else
g32p_row31_cosetLabels1Part0016 i)))))

def g32p_row31_cosetDistances1 : Fin 8640 → ℕ :=
  fun i => (if i.val < 4096 then
(if i.val < 2048 then
(if i.val < 1024 then
(if i.val < 512 then
g32p_row31_cosetDistances1Part0000 i
else
g32p_row31_cosetDistances1Part0001 i)
else
(if i.val < 1536 then
g32p_row31_cosetDistances1Part0002 i
else
g32p_row31_cosetDistances1Part0003 i))
else
(if i.val < 3072 then
(if i.val < 2560 then
g32p_row31_cosetDistances1Part0004 i
else
g32p_row31_cosetDistances1Part0005 i)
else
(if i.val < 3584 then
g32p_row31_cosetDistances1Part0006 i
else
g32p_row31_cosetDistances1Part0007 i)))
else
(if i.val < 6144 then
(if i.val < 5120 then
(if i.val < 4608 then
g32p_row31_cosetDistances1Part0008 i
else
g32p_row31_cosetDistances1Part0009 i)
else
(if i.val < 5632 then
g32p_row31_cosetDistances1Part0010 i
else
g32p_row31_cosetDistances1Part0011 i))
else
(if i.val < 7168 then
(if i.val < 6656 then
g32p_row31_cosetDistances1Part0012 i
else
g32p_row31_cosetDistances1Part0013 i)
else
(if i.val < 7680 then
g32p_row31_cosetDistances1Part0014 i
else
(if i.val < 8192 then
g32p_row31_cosetDistances1Part0015 i
else
g32p_row31_cosetDistances1Part0016 i)))))

def g32p_row31_cosetRoots1 : Fin 2880 → Fin 8640 :=
  fun i => (if i.val < 1536 then
(if i.val < 512 then
g32p_row31_cosetRoots1Part0000 i
else
(if i.val < 1024 then
g32p_row31_cosetRoots1Part0001 i
else
g32p_row31_cosetRoots1Part0002 i))
else
(if i.val < 2048 then
g32p_row31_cosetRoots1Part0003 i
else
(if i.val < 2560 then
g32p_row31_cosetRoots1Part0004 i
else
g32p_row31_cosetRoots1Part0005 i)))

def g32p_row31_cosetLengths1 : Fin 2880 → ℕ :=
  fun i => (if i.val < 1536 then
(if i.val < 512 then
g32p_row31_cosetLengths1Part0000 i
else
(if i.val < 1024 then
g32p_row31_cosetLengths1Part0001 i
else
g32p_row31_cosetLengths1Part0002 i))
else
(if i.val < 2048 then
g32p_row31_cosetLengths1Part0003 i
else
(if i.val < 2560 then
g32p_row31_cosetLengths1Part0004 i
else
g32p_row31_cosetLengths1Part0005 i)))

def g32p_row31_cosetCycleNodes1 : Fin 2880 → List ℕ :=
  fun i => (if i.val < 1536 then
(if i.val < 512 then
g32p_row31_cosetCycleNodes1Part0000 i
else
(if i.val < 1024 then
g32p_row31_cosetCycleNodes1Part0001 i
else
g32p_row31_cosetCycleNodes1Part0002 i))
else
(if i.val < 2048 then
g32p_row31_cosetCycleNodes1Part0003 i
else
(if i.val < 2560 then
g32p_row31_cosetCycleNodes1Part0004 i
else
g32p_row31_cosetCycleNodes1Part0005 i)))

def g32p_row31_cosetCycles1 : List (List ℕ) :=
  List.ofFn g32p_row31_cosetCycleNodes1

def g32p_row31_cosetMonodromies1 : Fin 2880 → Fin 18 :=
  fun i => (if i.val < 1536 then
(if i.val < 512 then
g32p_row31_cosetMonodromies1Part0000 i
else
(if i.val < 1024 then
g32p_row31_cosetMonodromies1Part0001 i
else
g32p_row31_cosetMonodromies1Part0002 i))
else
(if i.val < 2048 then
g32p_row31_cosetMonodromies1Part0003 i
else
(if i.val < 2560 then
g32p_row31_cosetMonodromies1Part0004 i
else
g32p_row31_cosetMonodromies1Part0005 i)))

def g32p_row31_cosetExponents1 : Fin 2880 → Multiplicative (ZMod 6) :=
  fun i => (if i.val < 1536 then
(if i.val < 512 then
g32p_row31_cosetExponents1Part0000 i
else
(if i.val < 1024 then
g32p_row31_cosetExponents1Part0001 i
else
g32p_row31_cosetExponents1Part0002 i))
else
(if i.val < 2048 then
g32p_row31_cosetExponents1Part0003 i
else
(if i.val < 2560 then
g32p_row31_cosetExponents1Part0004 i
else
g32p_row31_cosetExponents1Part0005 i)))

def g32p_row31_cosetLabels2 : Fin 8640 → Fin 4368 :=
  fun i => (if i.val < 4096 then
(if i.val < 2048 then
(if i.val < 1024 then
(if i.val < 512 then
g32p_row31_cosetLabels2Part0000 i
else
g32p_row31_cosetLabels2Part0001 i)
else
(if i.val < 1536 then
g32p_row31_cosetLabels2Part0002 i
else
g32p_row31_cosetLabels2Part0003 i))
else
(if i.val < 3072 then
(if i.val < 2560 then
g32p_row31_cosetLabels2Part0004 i
else
g32p_row31_cosetLabels2Part0005 i)
else
(if i.val < 3584 then
g32p_row31_cosetLabels2Part0006 i
else
g32p_row31_cosetLabels2Part0007 i)))
else
(if i.val < 6144 then
(if i.val < 5120 then
(if i.val < 4608 then
g32p_row31_cosetLabels2Part0008 i
else
g32p_row31_cosetLabels2Part0009 i)
else
(if i.val < 5632 then
g32p_row31_cosetLabels2Part0010 i
else
g32p_row31_cosetLabels2Part0011 i))
else
(if i.val < 7168 then
(if i.val < 6656 then
g32p_row31_cosetLabels2Part0012 i
else
g32p_row31_cosetLabels2Part0013 i)
else
(if i.val < 7680 then
g32p_row31_cosetLabels2Part0014 i
else
(if i.val < 8192 then
g32p_row31_cosetLabels2Part0015 i
else
g32p_row31_cosetLabels2Part0016 i)))))

def g32p_row31_cosetDistances2 : Fin 8640 → ℕ :=
  fun i => (if i.val < 4096 then
(if i.val < 2048 then
(if i.val < 1024 then
(if i.val < 512 then
g32p_row31_cosetDistances2Part0000 i
else
g32p_row31_cosetDistances2Part0001 i)
else
(if i.val < 1536 then
g32p_row31_cosetDistances2Part0002 i
else
g32p_row31_cosetDistances2Part0003 i))
else
(if i.val < 3072 then
(if i.val < 2560 then
g32p_row31_cosetDistances2Part0004 i
else
g32p_row31_cosetDistances2Part0005 i)
else
(if i.val < 3584 then
g32p_row31_cosetDistances2Part0006 i
else
g32p_row31_cosetDistances2Part0007 i)))
else
(if i.val < 6144 then
(if i.val < 5120 then
(if i.val < 4608 then
g32p_row31_cosetDistances2Part0008 i
else
g32p_row31_cosetDistances2Part0009 i)
else
(if i.val < 5632 then
g32p_row31_cosetDistances2Part0010 i
else
g32p_row31_cosetDistances2Part0011 i))
else
(if i.val < 7168 then
(if i.val < 6656 then
g32p_row31_cosetDistances2Part0012 i
else
g32p_row31_cosetDistances2Part0013 i)
else
(if i.val < 7680 then
g32p_row31_cosetDistances2Part0014 i
else
(if i.val < 8192 then
g32p_row31_cosetDistances2Part0015 i
else
g32p_row31_cosetDistances2Part0016 i)))))

def g32p_row31_cosetRoots2 : Fin 4368 → Fin 8640 :=
  fun i => (if i.val < 2048 then
(if i.val < 1024 then
(if i.val < 512 then
g32p_row31_cosetRoots2Part0000 i
else
g32p_row31_cosetRoots2Part0001 i)
else
(if i.val < 1536 then
g32p_row31_cosetRoots2Part0002 i
else
g32p_row31_cosetRoots2Part0003 i))
else
(if i.val < 3072 then
(if i.val < 2560 then
g32p_row31_cosetRoots2Part0004 i
else
g32p_row31_cosetRoots2Part0005 i)
else
(if i.val < 3584 then
g32p_row31_cosetRoots2Part0006 i
else
(if i.val < 4096 then
g32p_row31_cosetRoots2Part0007 i
else
g32p_row31_cosetRoots2Part0008 i))))

def g32p_row31_cosetLengths2 : Fin 4368 → ℕ :=
  fun i => (if i.val < 2048 then
(if i.val < 1024 then
(if i.val < 512 then
g32p_row31_cosetLengths2Part0000 i
else
g32p_row31_cosetLengths2Part0001 i)
else
(if i.val < 1536 then
g32p_row31_cosetLengths2Part0002 i
else
g32p_row31_cosetLengths2Part0003 i))
else
(if i.val < 3072 then
(if i.val < 2560 then
g32p_row31_cosetLengths2Part0004 i
else
g32p_row31_cosetLengths2Part0005 i)
else
(if i.val < 3584 then
g32p_row31_cosetLengths2Part0006 i
else
(if i.val < 4096 then
g32p_row31_cosetLengths2Part0007 i
else
g32p_row31_cosetLengths2Part0008 i))))

def g32p_row31_cosetCycleNodes2 : Fin 4368 → List ℕ :=
  fun i => (if i.val < 2048 then
(if i.val < 1024 then
(if i.val < 512 then
g32p_row31_cosetCycleNodes2Part0000 i
else
g32p_row31_cosetCycleNodes2Part0001 i)
else
(if i.val < 1536 then
g32p_row31_cosetCycleNodes2Part0002 i
else
g32p_row31_cosetCycleNodes2Part0003 i))
else
(if i.val < 3072 then
(if i.val < 2560 then
g32p_row31_cosetCycleNodes2Part0004 i
else
g32p_row31_cosetCycleNodes2Part0005 i)
else
(if i.val < 3584 then
g32p_row31_cosetCycleNodes2Part0006 i
else
(if i.val < 4096 then
g32p_row31_cosetCycleNodes2Part0007 i
else
g32p_row31_cosetCycleNodes2Part0008 i))))

def g32p_row31_cosetCycles2 : List (List ℕ) :=
  List.ofFn g32p_row31_cosetCycleNodes2

def g32p_row31_cosetMonodromies2 : Fin 4368 → Fin 18 :=
  fun i => (if i.val < 2048 then
(if i.val < 1024 then
(if i.val < 512 then
g32p_row31_cosetMonodromies2Part0000 i
else
g32p_row31_cosetMonodromies2Part0001 i)
else
(if i.val < 1536 then
g32p_row31_cosetMonodromies2Part0002 i
else
g32p_row31_cosetMonodromies2Part0003 i))
else
(if i.val < 3072 then
(if i.val < 2560 then
g32p_row31_cosetMonodromies2Part0004 i
else
g32p_row31_cosetMonodromies2Part0005 i)
else
(if i.val < 3584 then
g32p_row31_cosetMonodromies2Part0006 i
else
(if i.val < 4096 then
g32p_row31_cosetMonodromies2Part0007 i
else
g32p_row31_cosetMonodromies2Part0008 i))))

def g32p_row31_cosetExponents2 : Fin 4368 → Multiplicative (ZMod 6) :=
  fun i => (if i.val < 2048 then
(if i.val < 1024 then
(if i.val < 512 then
g32p_row31_cosetExponents2Part0000 i
else
g32p_row31_cosetExponents2Part0001 i)
else
(if i.val < 1536 then
g32p_row31_cosetExponents2Part0002 i
else
g32p_row31_cosetExponents2Part0003 i))
else
(if i.val < 3072 then
(if i.val < 2560 then
g32p_row31_cosetExponents2Part0004 i
else
g32p_row31_cosetExponents2Part0005 i)
else
(if i.val < 3584 then
g32p_row31_cosetExponents2Part0006 i
else
(if i.val < 4096 then
g32p_row31_cosetExponents2Part0007 i
else
g32p_row31_cosetExponents2Part0008 i))))


end HodgeLean.Foundations.Program

end
