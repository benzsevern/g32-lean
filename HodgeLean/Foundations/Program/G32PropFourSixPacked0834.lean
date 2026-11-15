import HodgeLean.Foundations.Program.HurwitzPrymRexG32Core

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row31_cosetWordsPart0033 : Fin 8640 → List (Fin 4) :=
  fun i => (if i.val < 4288 then
(if i.val < 4256 then
(if i.val < 4240 then
(if i.val < 4232 then
(if i.val < 4228 then
(if i.val < 4226 then
(if i.val < 4225 then
[3, 2, 2, 3, 0, 0, 1, 2]
else
[3, 2, 2, 3, 0, 0, 3, 2])
else
(if i.val < 4227 then
[3, 2, 2, 3, 0, 1, 1, 2]
else
[3, 2, 2, 3, 0, 1, 2, 2]))
else
(if i.val < 4230 then
(if i.val < 4229 then
[3, 2, 2, 3, 0, 1, 2, 3]
else
[3, 3, 0, 0, 1, 1, 2, 1])
else
(if i.val < 4231 then
[3, 3, 0, 0, 1, 1, 2, 2]
else
[3, 3, 0, 0, 1, 1, 2, 3])))
else
(if i.val < 4236 then
(if i.val < 4234 then
(if i.val < 4233 then
[3, 3, 0, 0, 1, 2, 1, 3]
else
[3, 3, 0, 0, 1, 2, 2, 1])
else
(if i.val < 4235 then
[3, 3, 0, 0, 1, 2, 2, 3]
else
[3, 3, 0, 0, 1, 2, 3, 0]))
else
(if i.val < 4238 then
(if i.val < 4237 then
[3, 3, 0, 0, 2, 1, 0, 0]
else
[3, 3, 0, 0, 2, 1, 1, 2])
else
(if i.val < 4239 then
[3, 3, 0, 0, 2, 1, 3, 2]
else
[3, 3, 0, 0, 2, 1, 3, 3]))))
else
(if i.val < 4248 then
(if i.val < 4244 then
(if i.val < 4242 then
(if i.val < 4241 then
[3, 3, 0, 0, 2, 2, 1, 0]
else
[3, 3, 0, 0, 2, 2, 1, 3])
else
(if i.val < 4243 then
[3, 3, 0, 0, 2, 3, 3, 2]
else
[3, 3, 0, 1, 1, 0, 2, 1]))
else
(if i.val < 4246 then
(if i.val < 4245 then
[3, 3, 0, 1, 1, 0, 2, 2]
else
[3, 3, 0, 1, 1, 0, 2, 3])
else
(if i.val < 4247 then
[3, 3, 0, 1, 1, 0, 3, 2]
else
[3, 3, 0, 1, 1, 2, 1, 1])))
else
(if i.val < 4252 then
(if i.val < 4250 then
(if i.val < 4249 then
[3, 3, 0, 1, 1, 2, 2, 1]
else
[3, 3, 0, 1, 1, 2, 2, 3])
else
(if i.val < 4251 then
[3, 3, 0, 1, 1, 2, 3, 0]
else
[3, 3, 0, 1, 2, 1, 0, 0]))
else
(if i.val < 4254 then
(if i.val < 4253 then
[3, 3, 0, 1, 2, 1, 1, 0]
else
[3, 3, 0, 1, 2, 1, 1, 2])
else
(if i.val < 4255 then
[3, 3, 0, 1, 2, 1, 1, 3]
else
[3, 3, 0, 1, 2, 1, 3, 0])))))
else
(if i.val < 4272 then
(if i.val < 4264 then
(if i.val < 4260 then
(if i.val < 4258 then
(if i.val < 4257 then
[3, 3, 0, 1, 2, 1, 3, 3]
else
[3, 3, 0, 1, 2, 2, 1, 0])
else
(if i.val < 4259 then
[3, 3, 0, 1, 2, 2, 1, 1]
else
[3, 3, 0, 1, 2, 2, 1, 3]))
else
(if i.val < 4262 then
(if i.val < 4261 then
[3, 3, 0, 1, 2, 2, 3, 3]
else
[3, 3, 0, 1, 2, 3, 0, 0])
else
(if i.val < 4263 then
[3, 3, 0, 1, 2, 3, 0, 1]
else
[3, 3, 0, 1, 2, 3, 3, 2])))
else
(if i.val < 4268 then
(if i.val < 4266 then
(if i.val < 4265 then
[3, 3, 0, 2, 1, 0, 3, 0]
else
[3, 3, 0, 2, 1, 0, 3, 3])
else
(if i.val < 4267 then
[3, 3, 0, 2, 1, 1, 0, 3]
else
[3, 3, 0, 2, 1, 1, 2, 3]))
else
(if i.val < 4270 then
(if i.val < 4269 then
[3, 3, 0, 2, 1, 1, 3, 2]
else
[3, 3, 0, 2, 1, 3, 0, 0])
else
(if i.val < 4271 then
[3, 3, 0, 2, 1, 3, 3, 2]
else
[3, 3, 0, 2, 2, 1, 0, 3]))))
else
(if i.val < 4280 then
(if i.val < 4276 then
(if i.val < 4274 then
(if i.val < 4273 then
[3, 3, 0, 2, 2, 1, 1, 0]
else
[3, 3, 0, 2, 2, 1, 1, 3])
else
(if i.val < 4275 then
[3, 3, 0, 2, 2, 1, 3, 0]
else
[3, 3, 0, 2, 2, 1, 3, 3]))
else
(if i.val < 4278 then
(if i.val < 4277 then
[3, 3, 0, 2, 2, 3, 3, 0]
else
[3, 3, 0, 2, 3, 3, 0, 2])
else
(if i.val < 4279 then
[3, 3, 0, 2, 3, 3, 2, 1]
else
[3, 3, 2, 1, 0, 0, 1, 3])))
else
(if i.val < 4284 then
(if i.val < 4282 then
(if i.val < 4281 then
[3, 3, 2, 1, 0, 3, 2, 2]
else
[3, 3, 2, 1, 0, 3, 3, 2])
else
(if i.val < 4283 then
[3, 3, 2, 1, 1, 0, 2, 3]
else
[3, 3, 2, 1, 1, 0, 3, 2]))
else
(if i.val < 4286 then
(if i.val < 4285 then
[3, 3, 2, 1, 1, 0, 3, 3]
else
[3, 3, 2, 1, 1, 2, 3, 3])
else
(if i.val < 4287 then
[3, 3, 2, 2, 1, 0, 0, 3]
else
[3, 3, 2, 2, 1, 0, 3, 2]))))))
else
(if i.val < 4320 then
(if i.val < 4304 then
(if i.val < 4296 then
(if i.val < 4292 then
(if i.val < 4290 then
(if i.val < 4289 then
[3, 3, 2, 2, 1, 0, 3, 3]
else
[3, 3, 2, 2, 1, 1, 0, 0])
else
(if i.val < 4291 then
[3, 3, 2, 2, 1, 1, 0, 3]
else
[0, 0, 1, 0, 0, 1, 2, 1, 0]))
else
(if i.val < 4294 then
(if i.val < 4293 then
[0, 0, 1, 0, 0, 1, 2, 1, 1]
else
[0, 0, 1, 0, 0, 1, 2, 1, 3])
else
(if i.val < 4295 then
[0, 0, 1, 0, 0, 1, 2, 2, 1]
else
[0, 0, 1, 0, 0, 1, 2, 2, 3])))
else
(if i.val < 4300 then
(if i.val < 4298 then
(if i.val < 4297 then
[0, 0, 1, 0, 0, 1, 2, 3, 3]
else
[0, 0, 1, 0, 0, 1, 3, 0, 2])
else
(if i.val < 4299 then
[0, 0, 1, 0, 0, 1, 3, 2, 1]
else
[0, 0, 1, 0, 0, 2, 1, 1, 2]))
else
(if i.val < 4302 then
(if i.val < 4301 then
[0, 0, 1, 0, 0, 2, 1, 1, 3]
else
[0, 0, 1, 0, 0, 2, 1, 3, 0])
else
(if i.val < 4303 then
[0, 0, 1, 0, 0, 2, 2, 1, 0]
else
[0, 0, 1, 0, 0, 2, 2, 1, 3]))))
else
(if i.val < 4312 then
(if i.val < 4308 then
(if i.val < 4306 then
(if i.val < 4305 then
[0, 0, 1, 0, 0, 2, 2, 3, 2]
else
[0, 0, 1, 0, 0, 2, 2, 3, 3])
else
(if i.val < 4307 then
[0, 0, 1, 0, 0, 2, 3, 2, 2]
else
[0, 0, 1, 0, 0, 2, 3, 3, 2]))
else
(if i.val < 4310 then
(if i.val < 4309 then
[0, 0, 1, 0, 0, 3, 0, 1, 2]
else
[0, 0, 1, 0, 0, 3, 0, 2, 1])
else
(if i.val < 4311 then
[0, 0, 1, 0, 0, 3, 0, 2, 3]
else
[0, 0, 1, 0, 0, 3, 2, 1, 1])))
else
(if i.val < 4316 then
(if i.val < 4314 then
(if i.val < 4313 then
[0, 0, 1, 0, 0, 3, 2, 2, 1]
else
[0, 0, 1, 0, 0, 3, 3, 0, 2])
else
(if i.val < 4315 then
[0, 0, 1, 0, 0, 3, 3, 2, 1]
else
[0, 0, 1, 0, 0, 3, 3, 2, 2]))
else
(if i.val < 4318 then
(if i.val < 4317 then
[0, 0, 1, 0, 2, 1, 0, 0, 3]
else
[0, 0, 1, 0, 2, 1, 0, 3, 2])
else
(if i.val < 4319 then
[0, 0, 1, 0, 2, 1, 1, 3, 2]
else
[0, 0, 1, 0, 2, 1, 1, 3, 3])))))
else
(if i.val < 4336 then
(if i.val < 4328 then
(if i.val < 4324 then
(if i.val < 4322 then
(if i.val < 4321 then
[0, 0, 1, 0, 2, 1, 3, 0, 0]
else
[0, 0, 1, 0, 2, 1, 3, 2, 2])
else
(if i.val < 4323 then
[0, 0, 1, 0, 2, 1, 3, 3, 2]
else
[0, 0, 1, 0, 2, 2, 1, 0, 0]))
else
(if i.val < 4326 then
(if i.val < 4325 then
[0, 0, 1, 0, 2, 2, 1, 0, 3]
else
[0, 0, 1, 0, 2, 2, 1, 1, 0])
else
(if i.val < 4327 then
[0, 0, 1, 0, 2, 2, 1, 3, 0]
else
[0, 0, 1, 0, 2, 2, 1, 3, 2])))
else
(if i.val < 4332 then
(if i.val < 4330 then
(if i.val < 4329 then
[0, 0, 1, 0, 2, 2, 3, 0, 0]
else
[0, 0, 1, 0, 2, 2, 3, 0, 1])
else
(if i.val < 4331 then
[0, 0, 1, 0, 2, 2, 3, 0, 2]
else
[0, 0, 1, 0, 2, 2, 3, 2, 1]))
else
(if i.val < 4334 then
(if i.val < 4333 then
[0, 0, 1, 0, 2, 2, 3, 3, 0]
else
[0, 0, 1, 0, 2, 2, 3, 3, 2])
else
(if i.val < 4335 then
[0, 0, 1, 0, 2, 3, 0, 0, 2]
else
[0, 0, 1, 0, 2, 3, 0, 0, 3]))))
else
(if i.val < 4344 then
(if i.val < 4340 then
(if i.val < 4338 then
(if i.val < 4337 then
[0, 0, 1, 0, 2, 3, 0, 1, 2]
else
[0, 0, 1, 0, 2, 3, 0, 2, 1])
else
(if i.val < 4339 then
[0, 0, 1, 0, 2, 3, 2, 1, 1]
else
[0, 0, 1, 0, 2, 3, 3, 2, 1]))
else
(if i.val < 4342 then
(if i.val < 4341 then
[0, 0, 1, 0, 2, 3, 3, 2, 2]
else
[0, 0, 1, 0, 3, 0, 0, 1, 2])
else
(if i.val < 4343 then
[0, 0, 1, 0, 3, 0, 0, 2, 1]
else
[0, 0, 1, 0, 3, 0, 0, 2, 2])))
else
(if i.val < 4348 then
(if i.val < 4346 then
(if i.val < 4345 then
[0, 0, 1, 0, 3, 0, 1, 1, 2]
else
[0, 0, 1, 0, 3, 0, 1, 2, 1])
else
(if i.val < 4347 then
[0, 0, 1, 0, 3, 0, 1, 2, 2]
else
[0, 0, 1, 0, 3, 0, 2, 1, 0]))
else
(if i.val < 4350 then
(if i.val < 4349 then
[0, 0, 1, 0, 3, 0, 2, 1, 1]
else
[0, 0, 1, 0, 3, 0, 2, 1, 3])
else
(if i.val < 4351 then
[0, 0, 1, 0, 3, 0, 2, 2, 1]
else
[0, 0, 1, 0, 3, 0, 2, 2, 3])))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row31_cosetWordsPart0034 : Fin 8640 → List (Fin 4) :=
  fun i => (if i.val < 4416 then
(if i.val < 4384 then
(if i.val < 4368 then
(if i.val < 4360 then
(if i.val < 4356 then
(if i.val < 4354 then
(if i.val < 4353 then
[0, 0, 1, 0, 3, 0, 2, 3, 3]
else
[0, 0, 1, 0, 3, 2, 1, 1, 0])
else
(if i.val < 4355 then
[0, 0, 1, 0, 3, 2, 2, 1, 0]
else
[0, 0, 1, 0, 3, 3, 0, 1, 2]))
else
(if i.val < 4358 then
(if i.val < 4357 then
[0, 0, 1, 0, 3, 3, 2, 2, 1]
else
[0, 0, 1, 1, 0, 0, 2, 1, 0])
else
(if i.val < 4359 then
[0, 0, 1, 1, 0, 0, 2, 1, 3]
else
[0, 0, 1, 1, 0, 0, 2, 2, 1])))
else
(if i.val < 4364 then
(if i.val < 4362 then
(if i.val < 4361 then
[0, 0, 1, 1, 0, 0, 2, 2, 3]
else
[0, 0, 1, 1, 0, 0, 2, 3, 0])
else
(if i.val < 4363 then
[0, 0, 1, 1, 0, 0, 2, 3, 3]
else
[0, 0, 1, 1, 0, 2, 1, 0, 0]))
else
(if i.val < 4366 then
(if i.val < 4365 then
[0, 0, 1, 1, 0, 2, 1, 1, 2]
else
[0, 0, 1, 1, 0, 2, 1, 3, 0])
else
(if i.val < 4367 then
[0, 0, 1, 1, 0, 2, 2, 1, 0]
else
[0, 0, 1, 1, 0, 2, 2, 1, 1]))))
else
(if i.val < 4376 then
(if i.val < 4372 then
(if i.val < 4370 then
(if i.val < 4369 then
[0, 0, 1, 1, 0, 2, 2, 1, 3]
else
[0, 0, 1, 1, 0, 2, 2, 3, 0])
else
(if i.val < 4371 then
[0, 0, 1, 1, 0, 2, 2, 3, 3]
else
[0, 0, 1, 1, 0, 2, 3, 0, 0]))
else
(if i.val < 4374 then
(if i.val < 4373 then
[0, 0, 1, 1, 0, 2, 3, 0, 1]
else
[0, 0, 1, 1, 0, 2, 3, 0, 2])
else
(if i.val < 4375 then
[0, 0, 1, 1, 0, 2, 3, 2, 1]
else
[0, 0, 1, 1, 0, 2, 3, 3, 2])))
else
(if i.val < 4380 then
(if i.val < 4378 then
(if i.val < 4377 then
[0, 0, 1, 1, 0, 3, 0, 1, 2]
else
[0, 0, 1, 1, 0, 3, 0, 2, 1])
else
(if i.val < 4379 then
[0, 0, 1, 1, 0, 3, 0, 2, 2]
else
[0, 0, 1, 1, 0, 3, 0, 2, 3]))
else
(if i.val < 4382 then
(if i.val < 4381 then
[0, 0, 1, 1, 0, 3, 2, 1, 0]
else
[0, 0, 1, 1, 0, 3, 2, 2, 1])
else
(if i.val < 4383 then
[0, 0, 1, 1, 0, 3, 2, 2, 3]
else
[0, 0, 1, 1, 2, 1, 0, 0, 3])))))
else
(if i.val < 4400 then
(if i.val < 4392 then
(if i.val < 4388 then
(if i.val < 4386 then
(if i.val < 4385 then
[0, 0, 1, 1, 2, 1, 0, 3, 0]
else
[0, 0, 1, 1, 2, 1, 0, 3, 2])
else
(if i.val < 4387 then
[0, 0, 1, 1, 2, 1, 0, 3, 3]
else
[0, 0, 1, 1, 2, 1, 1, 0, 0]))
else
(if i.val < 4390 then
(if i.val < 4389 then
[0, 0, 1, 1, 2, 1, 1, 3, 0]
else
[0, 0, 1, 1, 2, 1, 1, 3, 2])
else
(if i.val < 4391 then
[0, 0, 1, 1, 2, 1, 1, 3, 3]
else
[0, 0, 1, 1, 2, 1, 3, 0, 0])))
else
(if i.val < 4396 then
(if i.val < 4394 then
(if i.val < 4393 then
[0, 0, 1, 1, 2, 1, 3, 0, 2]
else
[0, 0, 1, 1, 2, 1, 3, 2, 2])
else
(if i.val < 4395 then
[0, 0, 1, 1, 2, 1, 3, 3, 0]
else
[0, 0, 1, 1, 2, 2, 1, 0, 0]))
else
(if i.val < 4398 then
(if i.val < 4397 then
[0, 0, 1, 1, 2, 2, 1, 1, 0]
else
[0, 0, 1, 1, 2, 2, 1, 3, 0])
else
(if i.val < 4399 then
[0, 0, 1, 1, 2, 2, 1, 3, 3]
else
[0, 0, 1, 1, 2, 2, 3, 0, 0]))))
else
(if i.val < 4408 then
(if i.val < 4404 then
(if i.val < 4402 then
(if i.val < 4401 then
[0, 0, 1, 1, 2, 2, 3, 0, 1]
else
[0, 0, 1, 1, 2, 2, 3, 0, 2])
else
(if i.val < 4403 then
[0, 0, 1, 1, 2, 2, 3, 2, 1]
else
[0, 0, 1, 1, 2, 2, 3, 3, 0]))
else
(if i.val < 4406 then
(if i.val < 4405 then
[0, 0, 1, 1, 2, 3, 0, 0, 2]
else
[0, 0, 1, 1, 2, 3, 0, 0, 3])
else
(if i.val < 4407 then
[0, 0, 1, 1, 2, 3, 2, 1, 0]
else
[0, 0, 1, 1, 2, 3, 2, 2, 1])))
else
(if i.val < 4412 then
(if i.val < 4410 then
(if i.val < 4409 then
[0, 0, 1, 1, 2, 3, 3, 0, 0]
else
[0, 0, 1, 1, 2, 3, 3, 2, 1])
else
(if i.val < 4411 then
[0, 0, 1, 1, 3, 0, 0, 2, 2]
else
[0, 0, 1, 1, 3, 0, 1, 2, 1]))
else
(if i.val < 4414 then
(if i.val < 4413 then
[0, 0, 1, 1, 3, 0, 1, 2, 2]
else
[0, 0, 1, 1, 3, 0, 2, 1, 1])
else
(if i.val < 4415 then
[0, 0, 1, 1, 3, 0, 2, 1, 3]
else
[0, 0, 1, 1, 3, 2, 1, 0, 0]))))))
else
(if i.val < 4448 then
(if i.val < 4432 then
(if i.val < 4424 then
(if i.val < 4420 then
(if i.val < 4418 then
(if i.val < 4417 then
[0, 0, 1, 1, 3, 2, 1, 1, 0]
else
[0, 0, 1, 1, 3, 2, 1, 1, 2])
else
(if i.val < 4419 then
[0, 0, 1, 1, 3, 2, 2, 1, 0]
else
[0, 0, 1, 1, 3, 2, 2, 3, 0]))
else
(if i.val < 4422 then
(if i.val < 4421 then
[0, 0, 1, 1, 3, 3, 0, 1, 2]
else
[0, 0, 1, 1, 3, 3, 0, 2, 1])
else
(if i.val < 4423 then
[0, 0, 1, 1, 3, 3, 0, 2, 2]
else
[0, 0, 1, 1, 3, 3, 2, 2, 1])))
else
(if i.val < 4428 then
(if i.val < 4426 then
(if i.val < 4425 then
[0, 0, 1, 2, 1, 0, 0, 1, 2]
else
[0, 0, 1, 2, 1, 0, 3, 0, 0])
else
(if i.val < 4427 then
[0, 0, 1, 2, 1, 0, 3, 0, 1]
else
[0, 0, 1, 2, 1, 1, 0, 0, 2]))
else
(if i.val < 4430 then
(if i.val < 4429 then
[0, 0, 1, 2, 1, 1, 0, 2, 1]
else
[0, 0, 1, 2, 1, 1, 0, 3, 2])
else
(if i.val < 4431 then
[0, 0, 1, 2, 1, 1, 0, 3, 3]
else
[0, 0, 1, 2, 1, 1, 2, 3, 0]))))
else
(if i.val < 4440 then
(if i.val < 4436 then
(if i.val < 4434 then
(if i.val < 4433 then
[0, 0, 1, 2, 1, 1, 2, 3, 3]
else
[0, 0, 1, 2, 1, 1, 3, 0, 1])
else
(if i.val < 4435 then
[0, 0, 1, 2, 1, 1, 3, 0, 2]
else
[0, 0, 1, 2, 1, 1, 3, 2, 1]))
else
(if i.val < 4438 then
(if i.val < 4437 then
[0, 0, 1, 2, 1, 1, 3, 2, 2]
else
[0, 0, 1, 2, 1, 1, 3, 3, 2])
else
(if i.val < 4439 then
[0, 0, 1, 2, 1, 3, 0, 1, 1]
else
[0, 0, 1, 2, 1, 3, 0, 1, 2])))
else
(if i.val < 4444 then
(if i.val < 4442 then
(if i.val < 4441 then
[0, 0, 1, 2, 1, 3, 0, 2, 2]
else
[0, 0, 1, 2, 1, 3, 3, 0, 1])
else
(if i.val < 4443 then
[0, 0, 1, 2, 1, 3, 3, 2, 1]
else
[0, 0, 1, 2, 1, 3, 3, 2, 2]))
else
(if i.val < 4446 then
(if i.val < 4445 then
[0, 0, 1, 2, 2, 1, 0, 0, 3]
else
[0, 0, 1, 2, 2, 1, 0, 3, 0])
else
(if i.val < 4447 then
[0, 0, 1, 2, 2, 1, 0, 3, 2]
else
[0, 0, 1, 2, 2, 1, 0, 3, 3])))))
else
(if i.val < 4464 then
(if i.val < 4456 then
(if i.val < 4452 then
(if i.val < 4450 then
(if i.val < 4449 then
[0, 0, 1, 2, 2, 1, 1, 0, 0]
else
[0, 0, 1, 2, 2, 1, 1, 3, 0])
else
(if i.val < 4451 then
[0, 0, 1, 2, 2, 1, 1, 3, 2]
else
[0, 0, 1, 2, 2, 1, 1, 3, 3]))
else
(if i.val < 4454 then
(if i.val < 4453 then
[0, 0, 1, 2, 2, 1, 3, 0, 0]
else
[0, 0, 1, 2, 2, 1, 3, 0, 1])
else
(if i.val < 4455 then
[0, 0, 1, 2, 2, 1, 3, 0, 2]
else
[0, 0, 1, 2, 2, 1, 3, 2, 2])))
else
(if i.val < 4460 then
(if i.val < 4458 then
(if i.val < 4457 then
[0, 0, 1, 2, 2, 1, 3, 3, 0]
else
[0, 0, 1, 2, 2, 1, 3, 3, 2])
else
(if i.val < 4459 then
[0, 0, 1, 2, 2, 3, 0, 0, 3]
else
[0, 0, 1, 2, 2, 3, 0, 2, 2]))
else
(if i.val < 4462 then
(if i.val < 4461 then
[0, 0, 1, 2, 2, 3, 2, 2, 1]
else
[0, 0, 1, 2, 2, 3, 3, 0, 0])
else
(if i.val < 4463 then
[0, 0, 1, 2, 2, 3, 3, 0, 1]
else
[0, 0, 1, 2, 2, 3, 3, 0, 2]))))
else
(if i.val < 4472 then
(if i.val < 4468 then
(if i.val < 4466 then
(if i.val < 4465 then
[0, 0, 1, 2, 3, 0, 0, 2, 2]
else
[0, 0, 1, 2, 3, 0, 1, 1, 2])
else
(if i.val < 4467 then
[0, 0, 1, 2, 3, 0, 1, 2, 1]
else
[0, 0, 1, 2, 3, 0, 1, 2, 2]))
else
(if i.val < 4470 then
(if i.val < 4469 then
[0, 0, 1, 2, 3, 2, 1, 0, 3]
else
[0, 0, 1, 2, 3, 2, 1, 1, 2])
else
(if i.val < 4471 then
[0, 0, 1, 2, 3, 2, 2, 1, 0]
else
[0, 0, 1, 2, 3, 2, 2, 1, 3])))
else
(if i.val < 4476 then
(if i.val < 4474 then
(if i.val < 4473 then
[0, 0, 1, 2, 3, 2, 2, 3, 0]
else
[0, 0, 1, 2, 3, 3, 0, 0, 2])
else
(if i.val < 4475 then
[0, 0, 1, 2, 3, 3, 0, 1, 2]
else
[0, 0, 1, 2, 3, 3, 0, 2, 1]))
else
(if i.val < 4478 then
(if i.val < 4477 then
[0, 0, 1, 2, 3, 3, 0, 2, 2]
else
[0, 0, 1, 2, 3, 3, 0, 2, 3])
else
(if i.val < 4479 then
[0, 0, 1, 2, 3, 3, 2, 1, 1]
else
[0, 0, 1, 2, 3, 3, 2, 2, 1])))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row31_cosetWordsPart0035 : Fin 8640 → List (Fin 4) :=
  fun i => (if i.val < 4544 then
(if i.val < 4512 then
(if i.val < 4496 then
(if i.val < 4488 then
(if i.val < 4484 then
(if i.val < 4482 then
(if i.val < 4481 then
[0, 0, 1, 3, 0, 0, 1, 1, 2]
else
[0, 0, 1, 3, 0, 0, 1, 2, 1])
else
(if i.val < 4483 then
[0, 0, 1, 3, 0, 0, 1, 2, 2]
else
[0, 0, 1, 3, 0, 0, 1, 3, 2]))
else
(if i.val < 4486 then
(if i.val < 4485 then
[0, 0, 1, 3, 0, 0, 3, 2, 1]
else
[0, 0, 1, 3, 0, 0, 3, 2, 2])
else
(if i.val < 4487 then
[0, 0, 1, 3, 0, 1, 1, 2, 1]
else
[0, 0, 1, 3, 0, 1, 1, 2, 3])))
else
(if i.val < 4492 then
(if i.val < 4490 then
(if i.val < 4489 then
[0, 0, 1, 3, 0, 1, 2, 1, 0]
else
[0, 0, 1, 3, 0, 1, 2, 1, 1])
else
(if i.val < 4491 then
[0, 0, 1, 3, 0, 1, 2, 1, 3]
else
[0, 0, 1, 3, 0, 1, 2, 2, 1]))
else
(if i.val < 4494 then
(if i.val < 4493 then
[0, 0, 1, 3, 0, 1, 2, 2, 3]
else
[0, 0, 1, 3, 0, 1, 2, 3, 3])
else
(if i.val < 4495 then
[0, 0, 1, 3, 0, 2, 1, 1, 2]
else
[0, 0, 1, 3, 0, 2, 1, 3, 2]))))
else
(if i.val < 4504 then
(if i.val < 4500 then
(if i.val < 4498 then
(if i.val < 4497 then
[0, 0, 1, 3, 0, 2, 2, 1, 1]
else
[0, 0, 1, 3, 0, 2, 2, 1, 3])
else
(if i.val < 4499 then
[0, 0, 1, 3, 0, 2, 3, 3, 0]
else
[0, 0, 1, 3, 2, 1, 0, 3, 2]))
else
(if i.val < 4502 then
(if i.val < 4501 then
[0, 0, 1, 3, 2, 1, 1, 2, 3]
else
[0, 0, 1, 3, 2, 2, 3, 0, 0])
else
(if i.val < 4503 then
[0, 0, 1, 3, 3, 0, 0, 2, 2]
else
[0, 0, 1, 3, 3, 0, 0, 2, 3])))
else
(if i.val < 4508 then
(if i.val < 4506 then
(if i.val < 4505 then
[0, 0, 1, 3, 3, 0, 1, 2, 1]
else
[0, 0, 1, 3, 3, 0, 1, 2, 3])
else
(if i.val < 4507 then
[0, 0, 1, 3, 3, 0, 2, 1, 1]
else
[0, 0, 1, 3, 3, 0, 2, 1, 3]))
else
(if i.val < 4510 then
(if i.val < 4509 then
[0, 0, 1, 3, 3, 0, 2, 2, 1]
else
[0, 0, 1, 3, 3, 2, 1, 0, 0])
else
(if i.val < 4511 then
[0, 0, 1, 3, 3, 2, 1, 0, 3]
else
[0, 0, 1, 3, 3, 2, 1, 1, 0])))))
else
(if i.val < 4528 then
(if i.val < 4520 then
(if i.val < 4516 then
(if i.val < 4514 then
(if i.val < 4513 then
[0, 0, 1, 3, 3, 2, 1, 1, 2]
else
[0, 0, 2, 1, 0, 0, 1, 2, 2])
else
(if i.val < 4515 then
[0, 0, 2, 1, 0, 0, 1, 2, 3]
else
[0, 0, 2, 1, 0, 0, 1, 3, 2]))
else
(if i.val < 4518 then
(if i.val < 4517 then
[0, 0, 2, 1, 0, 0, 3, 2, 1]
else
[0, 0, 2, 1, 0, 0, 3, 3, 2])
else
(if i.val < 4519 then
[0, 0, 2, 1, 0, 3, 0, 2, 1]
else
[0, 0, 2, 1, 0, 3, 0, 2, 2])))
else
(if i.val < 4524 then
(if i.val < 4522 then
(if i.val < 4521 then
[0, 0, 2, 1, 0, 3, 0, 2, 3]
else
[0, 0, 2, 1, 0, 3, 2, 1, 0])
else
(if i.val < 4523 then
[0, 0, 2, 1, 0, 3, 2, 1, 1]
else
[0, 0, 2, 1, 0, 3, 2, 2, 1]))
else
(if i.val < 4526 then
(if i.val < 4525 then
[0, 0, 2, 1, 0, 3, 2, 2, 3]
else
[0, 0, 2, 1, 1, 0, 0, 2, 1])
else
(if i.val < 4527 then
[0, 0, 2, 1, 1, 0, 0, 2, 3]
else
[0, 0, 2, 1, 1, 0, 2, 1, 1]))))
else
(if i.val < 4536 then
(if i.val < 4532 then
(if i.val < 4530 then
(if i.val < 4529 then
[0, 0, 2, 1, 1, 0, 2, 1, 3]
else
[0, 0, 2, 1, 1, 0, 3, 0, 2])
else
(if i.val < 4531 then
[0, 0, 2, 1, 1, 0, 3, 2, 1]
else
[0, 0, 2, 1, 1, 0, 3, 2, 2]))
else
(if i.val < 4534 then
(if i.val < 4533 then
[0, 0, 2, 1, 1, 0, 3, 3, 2]
else
[0, 0, 2, 1, 1, 2, 3, 0, 0])
else
(if i.val < 4535 then
[0, 0, 2, 1, 1, 2, 3, 0, 1]
else
[0, 0, 2, 1, 1, 2, 3, 0, 2])))
else
(if i.val < 4540 then
(if i.val < 4538 then
(if i.val < 4537 then
[0, 0, 2, 1, 1, 2, 3, 2, 1]
else
[0, 0, 2, 1, 1, 2, 3, 3, 0])
else
(if i.val < 4539 then
[0, 0, 2, 1, 1, 2, 3, 3, 2]
else
[0, 0, 2, 1, 1, 3, 0, 1, 2]))
else
(if i.val < 4542 then
(if i.val < 4541 then
[0, 0, 2, 1, 1, 3, 0, 2, 1]
else
[0, 0, 2, 1, 1, 3, 0, 2, 2])
else
(if i.val < 4543 then
[0, 0, 2, 1, 1, 3, 2, 1, 0]
else
[0, 0, 2, 1, 1, 3, 2, 2, 1]))))))
else
(if i.val < 4576 then
(if i.val < 4560 then
(if i.val < 4552 then
(if i.val < 4548 then
(if i.val < 4546 then
(if i.val < 4545 then
[0, 0, 2, 1, 1, 3, 2, 2, 3]
else
[0, 0, 2, 1, 3, 0, 0, 1, 2])
else
(if i.val < 4547 then
[0, 0, 2, 1, 3, 0, 0, 3, 2]
else
[0, 0, 2, 1, 3, 0, 1, 2, 1]))
else
(if i.val < 4550 then
(if i.val < 4549 then
[0, 0, 2, 1, 3, 0, 1, 2, 2]
else
[0, 0, 2, 1, 3, 0, 1, 2, 3])
else
(if i.val < 4551 then
[0, 0, 2, 1, 3, 0, 2, 1, 1]
else
[0, 0, 2, 1, 3, 2, 1, 1, 0])))
else
(if i.val < 4556 then
(if i.val < 4554 then
(if i.val < 4553 then
[0, 0, 2, 1, 3, 2, 1, 1, 2]
else
[0, 0, 2, 1, 3, 2, 2, 3, 0])
else
(if i.val < 4555 then
[0, 0, 2, 1, 3, 3, 0, 0, 2]
else
[0, 0, 2, 1, 3, 3, 0, 1, 2]))
else
(if i.val < 4558 then
(if i.val < 4557 then
[0, 0, 2, 1, 3, 3, 0, 2, 2]
else
[0, 0, 2, 1, 3, 3, 0, 2, 3])
else
(if i.val < 4559 then
[0, 0, 2, 1, 3, 3, 2, 1, 0]
else
[0, 0, 2, 1, 3, 3, 2, 2, 1]))))
else
(if i.val < 4568 then
(if i.val < 4564 then
(if i.val < 4562 then
(if i.val < 4561 then
[0, 0, 2, 2, 1, 0, 3, 0, 1]
else
[0, 0, 2, 2, 1, 0, 3, 0, 2])
else
(if i.val < 4563 then
[0, 0, 2, 2, 1, 0, 3, 2, 1]
else
[0, 0, 2, 2, 1, 0, 3, 2, 2]))
else
(if i.val < 4566 then
(if i.val < 4565 then
[0, 0, 2, 2, 1, 1, 0, 3, 2]
else
[0, 0, 2, 2, 1, 1, 3, 0, 2])
else
(if i.val < 4567 then
[0, 0, 2, 2, 1, 1, 3, 2, 1]
else
[0, 0, 2, 2, 1, 3, 0, 0, 2])))
else
(if i.val < 4572 then
(if i.val < 4570 then
(if i.val < 4569 then
[0, 0, 2, 2, 1, 3, 0, 1, 1]
else
[0, 0, 2, 2, 1, 3, 0, 1, 2])
else
(if i.val < 4571 then
[0, 0, 2, 2, 1, 3, 0, 2, 1]
else
[0, 0, 2, 2, 1, 3, 0, 2, 3]))
else
(if i.val < 4574 then
(if i.val < 4573 then
[0, 0, 2, 2, 1, 3, 2, 1, 0]
else
[0, 0, 2, 2, 1, 3, 2, 2, 3])
else
(if i.val < 4575 then
[0, 0, 2, 2, 1, 3, 3, 0, 2]
else
[0, 0, 2, 2, 1, 3, 3, 2, 1])))))
else
(if i.val < 4592 then
(if i.val < 4584 then
(if i.val < 4580 then
(if i.val < 4578 then
(if i.val < 4577 then
[0, 0, 2, 2, 3, 0, 0, 2, 2]
else
[0, 0, 2, 2, 3, 0, 0, 3, 2])
else
(if i.val < 4579 then
[0, 0, 2, 2, 3, 0, 1, 2, 1]
else
[0, 0, 2, 2, 3, 0, 1, 2, 3]))
else
(if i.val < 4582 then
(if i.val < 4581 then
[0, 0, 2, 2, 3, 0, 2, 1, 0]
else
[0, 0, 2, 2, 3, 0, 2, 1, 1])
else
(if i.val < 4583 then
[0, 0, 2, 2, 3, 0, 2, 2, 1]
else
[0, 0, 2, 2, 3, 2, 1, 0, 3])))
else
(if i.val < 4588 then
(if i.val < 4586 then
(if i.val < 4585 then
[0, 0, 2, 2, 3, 2, 2, 1, 0]
else
[0, 0, 2, 2, 3, 2, 2, 1, 3])
else
(if i.val < 4587 then
[0, 0, 2, 2, 3, 2, 2, 3, 0]
else
[0, 0, 2, 2, 3, 3, 0, 0, 2]))
else
(if i.val < 4590 then
(if i.val < 4589 then
[0, 0, 2, 2, 3, 3, 0, 1, 2]
else
[0, 0, 2, 2, 3, 3, 0, 2, 2])
else
(if i.val < 4591 then
[0, 0, 2, 2, 3, 3, 0, 2, 3]
else
[0, 0, 2, 2, 3, 3, 2, 1, 0]))))
else
(if i.val < 4600 then
(if i.val < 4596 then
(if i.val < 4594 then
(if i.val < 4593 then
[0, 0, 2, 2, 3, 3, 2, 1, 1]
else
[0, 0, 2, 2, 3, 3, 2, 2, 1])
else
(if i.val < 4595 then
[0, 0, 2, 3, 0, 0, 1, 1, 2]
else
[0, 0, 2, 3, 0, 0, 1, 2, 1]))
else
(if i.val < 4598 then
(if i.val < 4597 then
[0, 0, 2, 3, 0, 0, 2, 1, 0]
else
[0, 0, 2, 3, 0, 0, 2, 1, 1])
else
(if i.val < 4599 then
[0, 0, 2, 3, 0, 0, 2, 2, 3]
else
[0, 0, 2, 3, 0, 0, 3, 2, 1])))
else
(if i.val < 4604 then
(if i.val < 4602 then
(if i.val < 4601 then
[0, 0, 2, 3, 0, 1, 2, 1, 0]
else
[0, 0, 2, 3, 0, 1, 2, 1, 3])
else
(if i.val < 4603 then
[0, 0, 2, 3, 0, 1, 2, 2, 1]
else
[0, 0, 2, 3, 0, 1, 2, 2, 3]))
else
(if i.val < 4606 then
(if i.val < 4605 then
[0, 0, 2, 3, 0, 1, 2, 3, 0]
else
[0, 0, 2, 3, 0, 1, 2, 3, 3])
else
(if i.val < 4607 then
[0, 0, 2, 3, 0, 2, 1, 0, 0]
else
[0, 0, 2, 3, 0, 2, 1, 0, 3])))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row31_cosetWordsPart0036 : Fin 8640 → List (Fin 4) :=
  fun i => (if i.val < 4672 then
(if i.val < 4640 then
(if i.val < 4624 then
(if i.val < 4616 then
(if i.val < 4612 then
(if i.val < 4610 then
(if i.val < 4609 then
[0, 0, 2, 3, 0, 2, 2, 1, 3]
else
[0, 0, 2, 3, 0, 2, 2, 3, 0])
else
(if i.val < 4611 then
[0, 0, 2, 3, 0, 2, 2, 3, 3]
else
[0, 0, 2, 3, 2, 1, 1, 0, 0]))
else
(if i.val < 4614 then
(if i.val < 4613 then
[0, 0, 2, 3, 2, 1, 1, 0, 3]
else
[0, 0, 2, 3, 2, 1, 1, 2, 3])
else
(if i.val < 4615 then
[0, 0, 2, 3, 2, 2, 1, 0, 0]
else
[0, 0, 2, 3, 2, 2, 1, 0, 3])))
else
(if i.val < 4620 then
(if i.val < 4618 then
(if i.val < 4617 then
[0, 0, 2, 3, 2, 2, 1, 1, 0]
else
[0, 0, 2, 3, 2, 2, 1, 1, 3])
else
(if i.val < 4619 then
[0, 0, 2, 3, 2, 2, 1, 3, 0]
else
[0, 0, 2, 3, 3, 0, 0, 2, 1]))
else
(if i.val < 4622 then
(if i.val < 4621 then
[0, 0, 2, 3, 3, 0, 0, 2, 3]
else
[0, 0, 2, 3, 3, 0, 1, 1, 2])
else
(if i.val < 4623 then
[0, 0, 2, 3, 3, 0, 1, 2, 1]
else
[0, 0, 2, 3, 3, 0, 1, 2, 3]))))
else
(if i.val < 4632 then
(if i.val < 4628 then
(if i.val < 4626 then
(if i.val < 4625 then
[0, 0, 2, 3, 3, 0, 2, 1, 0]
else
[0, 0, 2, 3, 3, 0, 2, 1, 1])
else
(if i.val < 4627 then
[0, 0, 2, 3, 3, 0, 2, 1, 3]
else
[0, 0, 2, 3, 3, 0, 2, 2, 1]))
else
(if i.val < 4630 then
(if i.val < 4629 then
[0, 0, 2, 3, 3, 0, 2, 2, 3]
else
[0, 0, 2, 3, 3, 2, 1, 0, 0])
else
(if i.val < 4631 then
[0, 0, 2, 3, 3, 2, 1, 0, 3]
else
[0, 0, 2, 3, 3, 2, 2, 1, 0])))
else
(if i.val < 4636 then
(if i.val < 4634 then
(if i.val < 4633 then
[0, 0, 3, 0, 0, 1, 1, 2, 3]
else
[0, 0, 3, 0, 0, 1, 2, 1, 1])
else
(if i.val < 4635 then
[0, 0, 3, 0, 0, 1, 2, 2, 1]
else
[0, 0, 3, 0, 0, 1, 2, 3, 3]))
else
(if i.val < 4638 then
(if i.val < 4637 then
[0, 0, 3, 0, 0, 1, 3, 2, 1]
else
[0, 0, 3, 0, 0, 1, 3, 2, 2])
else
(if i.val < 4639 then
[0, 0, 3, 0, 0, 2, 1, 0, 0]
else
[0, 0, 3, 0, 0, 2, 1, 1, 2])))))
else
(if i.val < 4656 then
(if i.val < 4648 then
(if i.val < 4644 then
(if i.val < 4642 then
(if i.val < 4641 then
[0, 0, 3, 0, 0, 2, 2, 1, 0]
else
[0, 0, 3, 0, 0, 2, 2, 1, 1])
else
(if i.val < 4643 then
[0, 0, 3, 0, 0, 2, 2, 1, 3]
else
[0, 0, 3, 0, 0, 2, 2, 3, 3]))
else
(if i.val < 4646 then
(if i.val < 4645 then
[0, 0, 3, 0, 0, 2, 3, 2, 1]
else
[0, 0, 3, 0, 0, 2, 3, 3, 2])
else
(if i.val < 4647 then
[0, 0, 3, 0, 0, 3, 2, 1, 0]
else
[0, 0, 3, 0, 0, 3, 2, 1, 1])))
else
(if i.val < 4652 then
(if i.val < 4650 then
(if i.val < 4649 then
[0, 0, 3, 0, 0, 3, 2, 2, 1]
else
[0, 0, 3, 0, 1, 1, 0, 3, 2])
else
(if i.val < 4651 then
[0, 0, 3, 0, 1, 1, 2, 2, 1]
else
[0, 0, 3, 0, 1, 1, 2, 2, 3]))
else
(if i.val < 4654 then
(if i.val < 4653 then
[0, 0, 3, 0, 1, 2, 1, 1, 0]
else
[0, 0, 3, 0, 1, 2, 1, 1, 3])
else
(if i.val < 4655 then
[0, 0, 3, 0, 1, 2, 1, 3, 3]
else
[0, 0, 3, 0, 1, 2, 2, 1, 1]))))
else
(if i.val < 4664 then
(if i.val < 4660 then
(if i.val < 4658 then
(if i.val < 4657 then
[0, 0, 3, 0, 1, 2, 2, 3, 0]
else
[0, 0, 3, 0, 1, 2, 2, 3, 3])
else
(if i.val < 4659 then
[0, 0, 3, 0, 1, 2, 3, 0, 0]
else
[0, 0, 3, 0, 1, 2, 3, 0, 1]))
else
(if i.val < 4662 then
(if i.val < 4661 then
[0, 0, 3, 0, 1, 2, 3, 3, 0]
else
[0, 0, 3, 0, 2, 1, 1, 3, 2])
else
(if i.val < 4663 then
[0, 0, 3, 0, 2, 1, 3, 0, 0]
else
[0, 0, 3, 0, 2, 2, 1, 0, 0])))
else
(if i.val < 4668 then
(if i.val < 4666 then
(if i.val < 4665 then
[0, 0, 3, 0, 2, 2, 1, 0, 3]
else
[0, 0, 3, 0, 2, 2, 1, 1, 0])
else
(if i.val < 4667 then
[0, 0, 3, 0, 2, 2, 1, 3, 0]
else
[0, 0, 3, 0, 2, 2, 1, 3, 2]))
else
(if i.val < 4670 then
(if i.val < 4669 then
[0, 0, 3, 0, 2, 2, 3, 0, 1]
else
[0, 0, 3, 0, 2, 2, 3, 3, 0])
else
(if i.val < 4671 then
[0, 0, 3, 0, 2, 3, 3, 0, 2]
else
[0, 0, 3, 0, 2, 3, 3, 2, 1]))))))
else
(if i.val < 4704 then
(if i.val < 4688 then
(if i.val < 4680 then
(if i.val < 4676 then
(if i.val < 4674 then
(if i.val < 4673 then
[0, 0, 3, 2, 1, 0, 0, 3, 2]
else
[0, 0, 3, 2, 1, 0, 3, 2, 1])
else
(if i.val < 4675 then
[0, 0, 3, 2, 1, 0, 3, 2, 2]
else
[0, 0, 3, 2, 1, 1, 0, 2, 1]))
else
(if i.val < 4678 then
(if i.val < 4677 then
[0, 0, 3, 2, 1, 1, 0, 3, 2]
else
[0, 0, 3, 2, 1, 1, 0, 3, 3])
else
(if i.val < 4679 then
[0, 0, 3, 2, 1, 1, 2, 3, 0]
else
[0, 0, 3, 2, 2, 1, 0, 0, 3])))
else
(if i.val < 4684 then
(if i.val < 4682 then
(if i.val < 4681 then
[0, 0, 3, 2, 2, 1, 0, 3, 0]
else
[0, 0, 3, 2, 2, 1, 0, 3, 3])
else
(if i.val < 4683 then
[0, 0, 3, 2, 2, 1, 1, 0, 0]
else
[0, 0, 3, 2, 2, 1, 1, 3, 0]))
else
(if i.val < 4686 then
(if i.val < 4685 then
[0, 0, 3, 2, 2, 1, 1, 3, 2]
else
[0, 0, 3, 2, 2, 1, 3, 0, 0])
else
(if i.val < 4687 then
[0, 0, 3, 2, 2, 1, 3, 0, 1]
else
[0, 0, 3, 2, 2, 1, 3, 0, 2]))))
else
(if i.val < 4696 then
(if i.val < 4692 then
(if i.val < 4690 then
(if i.val < 4689 then
[0, 0, 3, 2, 2, 3, 0, 0, 3]
else
[0, 0, 3, 2, 2, 3, 0, 1, 2])
else
(if i.val < 4691 then
[0, 0, 3, 3, 0, 0, 2, 1, 0]
else
[0, 0, 3, 3, 0, 0, 2, 1, 3]))
else
(if i.val < 4694 then
(if i.val < 4693 then
[0, 0, 3, 3, 0, 0, 2, 2, 1]
else
[0, 0, 3, 3, 0, 0, 2, 3, 3])
else
(if i.val < 4695 then
[0, 0, 3, 3, 0, 1, 2, 1, 0]
else
[0, 0, 3, 3, 0, 1, 2, 1, 3])))
else
(if i.val < 4700 then
(if i.val < 4698 then
(if i.val < 4697 then
[0, 0, 3, 3, 0, 1, 2, 2, 3]
else
[0, 0, 3, 3, 0, 1, 2, 3, 0])
else
(if i.val < 4699 then
[0, 0, 3, 3, 0, 2, 1, 0, 0]
else
[0, 0, 3, 3, 0, 2, 1, 1, 2]))
else
(if i.val < 4702 then
(if i.val < 4701 then
[0, 0, 3, 3, 0, 2, 1, 3, 0]
else
[0, 0, 3, 3, 0, 2, 2, 1, 0])
else
(if i.val < 4703 then
[0, 0, 3, 3, 0, 2, 2, 1, 1]
else
[0, 0, 3, 3, 0, 2, 2, 1, 3])))))
else
(if i.val < 4720 then
(if i.val < 4712 then
(if i.val < 4708 then
(if i.val < 4706 then
(if i.val < 4705 then
[0, 0, 3, 3, 0, 2, 2, 3, 3]
else
[0, 0, 3, 3, 0, 2, 3, 3, 2])
else
(if i.val < 4707 then
[0, 0, 3, 3, 2, 1, 0, 0, 3]
else
[0, 0, 3, 3, 2, 1, 0, 3, 3]))
else
(if i.val < 4710 then
(if i.val < 4709 then
[0, 0, 3, 3, 2, 1, 1, 0, 0]
else
[0, 0, 3, 3, 2, 2, 1, 0, 0])
else
(if i.val < 4711 then
[0, 0, 3, 3, 2, 2, 1, 0, 3]
else
[0, 0, 3, 3, 2, 2, 1, 1, 0])))
else
(if i.val < 4716 then
(if i.val < 4714 then
(if i.val < 4713 then
[0, 1, 0, 0, 1, 2, 1, 0, 0]
else
[0, 1, 0, 0, 1, 2, 1, 0, 3])
else
(if i.val < 4715 then
[0, 1, 0, 0, 1, 2, 1, 1, 2]
else
[0, 1, 0, 0, 1, 2, 1, 3, 0]))
else
(if i.val < 4718 then
(if i.val < 4717 then
[0, 1, 0, 0, 1, 2, 1, 3, 2]
else
[0, 1, 0, 0, 1, 2, 2, 1, 0])
else
(if i.val < 4719 then
[0, 1, 0, 0, 1, 2, 2, 1, 1]
else
[0, 1, 0, 0, 1, 2, 2, 1, 3]))))
else
(if i.val < 4728 then
(if i.val < 4724 then
(if i.val < 4722 then
(if i.val < 4721 then
[0, 1, 0, 0, 1, 2, 2, 3, 0]
else
[0, 1, 0, 0, 1, 2, 2, 3, 3])
else
(if i.val < 4723 then
[0, 1, 0, 0, 1, 2, 3, 0, 0]
else
[0, 1, 0, 0, 1, 2, 3, 0, 1]))
else
(if i.val < 4726 then
(if i.val < 4725 then
[0, 1, 0, 0, 1, 2, 3, 0, 2]
else
[0, 1, 0, 0, 1, 2, 3, 2, 1])
else
(if i.val < 4727 then
[0, 1, 0, 0, 1, 2, 3, 3, 2]
else
[0, 1, 0, 0, 1, 3, 0, 0, 2])))
else
(if i.val < 4732 then
(if i.val < 4730 then
(if i.val < 4729 then
[0, 1, 0, 0, 1, 3, 0, 2, 1]
else
[0, 1, 0, 0, 1, 3, 0, 2, 2])
else
(if i.val < 4731 then
[0, 1, 0, 0, 1, 3, 0, 2, 3]
else
[0, 1, 0, 0, 1, 3, 2, 2, 1]))
else
(if i.val < 4734 then
(if i.val < 4733 then
[0, 1, 0, 0, 1, 3, 2, 2, 3]
else
[0, 1, 0, 0, 2, 1, 0, 3, 0])
else
(if i.val < 4735 then
[0, 1, 0, 0, 2, 1, 0, 3, 2]
else
[0, 1, 0, 0, 2, 1, 0, 3, 3])))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row31_cosetWordsPart0037 : Fin 8640 → List (Fin 4) :=
  fun i => (if i.val < 4800 then
(if i.val < 4768 then
(if i.val < 4752 then
(if i.val < 4744 then
(if i.val < 4740 then
(if i.val < 4738 then
(if i.val < 4737 then
[0, 1, 0, 0, 2, 1, 1, 0, 2]
else
[0, 1, 0, 0, 2, 1, 1, 0, 3])
else
(if i.val < 4739 then
[0, 1, 0, 0, 2, 1, 1, 2, 3]
else
[0, 1, 0, 0, 2, 1, 3, 0, 0]))
else
(if i.val < 4742 then
(if i.val < 4741 then
[0, 1, 0, 0, 2, 1, 3, 0, 1]
else
[0, 1, 0, 0, 2, 1, 3, 0, 2])
else
(if i.val < 4743 then
[0, 1, 0, 0, 2, 2, 1, 0, 0]
else
[0, 1, 0, 0, 2, 2, 1, 0, 3])))
else
(if i.val < 4748 then
(if i.val < 4746 then
(if i.val < 4745 then
[0, 1, 0, 0, 2, 2, 1, 1, 3]
else
[0, 1, 0, 0, 2, 2, 1, 3, 0])
else
(if i.val < 4747 then
[0, 1, 0, 0, 2, 2, 1, 3, 2]
else
[0, 1, 0, 0, 2, 2, 1, 3, 3]))
else
(if i.val < 4750 then
(if i.val < 4749 then
[0, 1, 0, 0, 2, 2, 3, 0, 0]
else
[0, 1, 0, 0, 2, 2, 3, 2, 2])
else
(if i.val < 4751 then
[0, 1, 0, 0, 2, 2, 3, 3, 2]
else
[0, 1, 0, 0, 2, 3, 0, 0, 3]))))
else
(if i.val < 4760 then
(if i.val < 4756 then
(if i.val < 4754 then
(if i.val < 4753 then
[0, 1, 0, 0, 2, 3, 0, 1, 1]
else
[0, 1, 0, 0, 2, 3, 0, 1, 2])
else
(if i.val < 4755 then
[0, 1, 0, 0, 2, 3, 0, 2, 2]
else
[0, 1, 0, 0, 2, 3, 2, 2, 1]))
else
(if i.val < 4758 then
(if i.val < 4757 then
[0, 1, 0, 0, 2, 3, 2, 2, 3]
else
[0, 1, 0, 0, 2, 3, 3, 2, 1])
else
(if i.val < 4759 then
[0, 1, 0, 0, 2, 3, 3, 2, 2]
else
[0, 1, 0, 0, 3, 0, 0, 3, 2])))
else
(if i.val < 4764 then
(if i.val < 4762 then
(if i.val < 4761 then
[0, 1, 0, 0, 3, 0, 1, 2, 1]
else
[0, 1, 0, 0, 3, 0, 1, 2, 2])
else
(if i.val < 4763 then
[0, 1, 0, 0, 3, 0, 1, 2, 3]
else
[0, 1, 0, 0, 3, 0, 2, 2, 1]))
else
(if i.val < 4766 then
(if i.val < 4765 then
[0, 1, 0, 0, 3, 0, 2, 2, 3]
else
[0, 1, 0, 0, 3, 2, 1, 1, 2])
else
(if i.val < 4767 then
[0, 1, 0, 0, 3, 3, 0, 2, 1]
else
[0, 1, 0, 0, 3, 3, 0, 2, 2])))))
else
(if i.val < 4784 then
(if i.val < 4776 then
(if i.val < 4772 then
(if i.val < 4770 then
(if i.val < 4769 then
[0, 1, 0, 0, 3, 3, 0, 2, 3]
else
[0, 1, 0, 0, 3, 3, 2, 1, 0])
else
(if i.val < 4771 then
[0, 1, 0, 0, 3, 3, 2, 1, 1]
else
[0, 1, 0, 0, 3, 3, 2, 2, 1]))
else
(if i.val < 4774 then
(if i.val < 4773 then
[0, 1, 0, 2, 1, 0, 0, 1, 2]
else
[0, 1, 0, 2, 1, 0, 0, 1, 3])
else
(if i.val < 4775 then
[0, 1, 0, 2, 1, 0, 3, 0, 0]
else
[0, 1, 0, 2, 1, 0, 3, 0, 1])))
else
(if i.val < 4780 then
(if i.val < 4778 then
(if i.val < 4777 then
[0, 1, 0, 2, 1, 0, 3, 2, 2]
else
[0, 1, 0, 2, 1, 0, 3, 3, 2])
else
(if i.val < 4779 then
[0, 1, 0, 2, 1, 1, 0, 0, 2]
else
[0, 1, 0, 2, 1, 1, 0, 2, 1]))
else
(if i.val < 4782 then
(if i.val < 4781 then
[0, 1, 0, 2, 1, 1, 0, 2, 3]
else
[0, 1, 0, 2, 1, 1, 0, 3, 2])
else
(if i.val < 4783 then
[0, 1, 0, 2, 1, 1, 2, 3, 0]
else
[0, 1, 0, 2, 1, 1, 2, 3, 3]))))
else
(if i.val < 4792 then
(if i.val < 4788 then
(if i.val < 4786 then
(if i.val < 4785 then
[0, 1, 0, 2, 1, 1, 3, 0, 1]
else
[0, 1, 0, 2, 1, 1, 3, 3, 2])
else
(if i.val < 4787 then
[0, 1, 0, 2, 1, 3, 0, 1, 2]
else
[0, 1, 0, 2, 1, 3, 2, 2, 1]))
else
(if i.val < 4790 then
(if i.val < 4789 then
[0, 1, 0, 2, 1, 3, 2, 2, 3]
else
[0, 1, 0, 2, 1, 3, 3, 0, 1])
else
(if i.val < 4791 then
[0, 1, 0, 2, 1, 3, 3, 2, 1]
else
[0, 1, 0, 2, 1, 3, 3, 2, 2])))
else
(if i.val < 4796 then
(if i.val < 4794 then
(if i.val < 4793 then
[0, 1, 0, 2, 2, 1, 0, 0, 3]
else
[0, 1, 0, 2, 2, 1, 0, 3, 0])
else
(if i.val < 4795 then
[0, 1, 0, 2, 2, 1, 0, 3, 2]
else
[0, 1, 0, 2, 2, 1, 0, 3, 3]))
else
(if i.val < 4798 then
(if i.val < 4797 then
[0, 1, 0, 2, 2, 1, 1, 0, 3]
else
[0, 1, 0, 2, 2, 1, 1, 3, 0])
else
(if i.val < 4799 then
[0, 1, 0, 2, 2, 1, 1, 3, 2]
else
[0, 1, 0, 2, 2, 1, 3, 0, 0]))))))
else
(if i.val < 4832 then
(if i.val < 4816 then
(if i.val < 4808 then
(if i.val < 4804 then
(if i.val < 4802 then
(if i.val < 4801 then
[0, 1, 0, 2, 2, 1, 3, 0, 1]
else
[0, 1, 0, 2, 2, 1, 3, 0, 2])
else
(if i.val < 4803 then
[0, 1, 0, 2, 2, 1, 3, 2, 2]
else
[0, 1, 0, 2, 2, 1, 3, 3, 0]))
else
(if i.val < 4806 then
(if i.val < 4805 then
[0, 1, 0, 2, 2, 1, 3, 3, 2]
else
[0, 1, 0, 2, 2, 3, 0, 0, 2])
else
(if i.val < 4807 then
[0, 1, 0, 2, 2, 3, 0, 0, 3]
else
[0, 1, 0, 2, 2, 3, 0, 1, 1])))
else
(if i.val < 4812 then
(if i.val < 4810 then
(if i.val < 4809 then
[0, 1, 0, 2, 2, 3, 0, 1, 2]
else
[0, 1, 0, 2, 2, 3, 0, 2, 1])
else
(if i.val < 4811 then
[0, 1, 0, 2, 2, 3, 0, 2, 2]
else
[0, 1, 0, 2, 2, 3, 2, 2, 1]))
else
(if i.val < 4814 then
(if i.val < 4813 then
[0, 1, 0, 2, 2, 3, 3, 0, 1]
else
[0, 1, 0, 2, 2, 3, 3, 2, 2])
else
(if i.val < 4815 then
[0, 1, 0, 2, 3, 0, 0, 2, 3]
else
[0, 1, 0, 2, 3, 0, 1, 1, 2]))))
else
(if i.val < 4824 then
(if i.val < 4820 then
(if i.val < 4818 then
(if i.val < 4817 then
[0, 1, 0, 2, 3, 0, 1, 2, 1]
else
[0, 1, 0, 2, 3, 0, 1, 2, 2])
else
(if i.val < 4819 then
[0, 1, 0, 2, 3, 0, 1, 2, 3]
else
[0, 1, 0, 2, 3, 0, 2, 1, 1]))
else
(if i.val < 4822 then
(if i.val < 4821 then
[0, 1, 0, 2, 3, 2, 1, 0, 3]
else
[0, 1, 0, 2, 3, 2, 1, 1, 0])
else
(if i.val < 4823 then
[0, 1, 0, 2, 3, 2, 2, 3, 0]
else
[0, 1, 0, 2, 3, 3, 0, 1, 2])))
else
(if i.val < 4828 then
(if i.val < 4826 then
(if i.val < 4825 then
[0, 1, 0, 2, 3, 3, 0, 2, 1]
else
[0, 1, 0, 2, 3, 3, 0, 2, 2])
else
(if i.val < 4827 then
[0, 1, 0, 2, 3, 3, 0, 2, 3]
else
[0, 1, 0, 2, 3, 3, 2, 1, 1]))
else
(if i.val < 4830 then
(if i.val < 4829 then
[0, 1, 0, 3, 0, 0, 1, 1, 2]
else
[0, 1, 0, 3, 0, 0, 1, 2, 1])
else
(if i.val < 4831 then
[0, 1, 0, 3, 0, 0, 1, 2, 2]
else
[0, 1, 0, 3, 0, 0, 2, 1, 1])))))
else
(if i.val < 4848 then
(if i.val < 4840 then
(if i.val < 4836 then
(if i.val < 4834 then
(if i.val < 4833 then
[0, 1, 0, 3, 0, 0, 2, 3, 2]
else
[0, 1, 0, 3, 0, 0, 2, 3, 3])
else
(if i.val < 4835 then
[0, 1, 0, 3, 0, 0, 3, 2, 2]
else
[0, 1, 0, 3, 0, 1, 1, 2, 1]))
else
(if i.val < 4838 then
(if i.val < 4837 then
[0, 1, 0, 3, 0, 1, 1, 2, 2]
else
[0, 1, 0, 3, 0, 1, 1, 2, 3])
else
(if i.val < 4839 then
[0, 1, 0, 3, 0, 1, 2, 1, 0]
else
[0, 1, 0, 3, 0, 1, 2, 1, 1])))
else
(if i.val < 4844 then
(if i.val < 4842 then
(if i.val < 4841 then
[0, 1, 0, 3, 0, 1, 2, 2, 1]
else
[0, 1, 0, 3, 0, 1, 2, 2, 3])
else
(if i.val < 4843 then
[0, 1, 0, 3, 0, 1, 2, 3, 3]
else
[0, 1, 0, 3, 0, 2, 1, 0, 0]))
else
(if i.val < 4846 then
(if i.val < 4845 then
[0, 1, 0, 3, 0, 2, 1, 1, 0]
else
[0, 1, 0, 3, 0, 2, 1, 3, 0])
else
(if i.val < 4847 then
[0, 1, 0, 3, 0, 2, 2, 1, 3]
else
[0, 1, 0, 3, 0, 2, 2, 3, 0]))))
else
(if i.val < 4856 then
(if i.val < 4852 then
(if i.val < 4850 then
(if i.val < 4849 then
[0, 1, 0, 3, 0, 2, 2, 3, 3]
else
[0, 1, 0, 3, 0, 2, 3, 3, 0])
else
(if i.val < 4851 then
[0, 1, 0, 3, 2, 1, 0, 0, 3]
else
[0, 1, 0, 3, 2, 1, 0, 3, 2]))
else
(if i.val < 4854 then
(if i.val < 4853 then
[0, 1, 0, 3, 2, 1, 1, 0, 0]
else
[0, 1, 0, 3, 2, 1, 1, 0, 3])
else
(if i.val < 4855 then
[0, 1, 0, 3, 2, 1, 1, 2, 3]
else
[0, 1, 0, 3, 2, 2, 3, 0, 0])))
else
(if i.val < 4860 then
(if i.val < 4858 then
(if i.val < 4857 then
[0, 1, 0, 3, 2, 2, 3, 0, 1]
else
[0, 1, 0, 3, 3, 0, 0, 2, 1])
else
(if i.val < 4859 then
[0, 1, 0, 3, 3, 0, 0, 2, 2]
else
[0, 1, 0, 3, 3, 0, 1, 2, 1]))
else
(if i.val < 4862 then
(if i.val < 4861 then
[0, 1, 0, 3, 3, 0, 1, 2, 3]
else
[0, 1, 0, 3, 3, 0, 2, 1, 0])
else
(if i.val < 4863 then
[0, 1, 0, 3, 3, 0, 2, 2, 1]
else
[0, 1, 0, 3, 3, 0, 2, 3, 3])))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row31_cosetWordsPart0038 : Fin 8640 → List (Fin 4) :=
  fun i => (if i.val < 4928 then
(if i.val < 4896 then
(if i.val < 4880 then
(if i.val < 4872 then
(if i.val < 4868 then
(if i.val < 4866 then
(if i.val < 4865 then
[0, 1, 0, 3, 3, 2, 1, 0, 3]
else
[0, 1, 0, 3, 3, 2, 1, 1, 0])
else
(if i.val < 4867 then
[0, 1, 0, 3, 3, 2, 1, 1, 2]
else
[0, 1, 0, 3, 3, 2, 2, 1, 1]))
else
(if i.val < 4870 then
(if i.val < 4869 then
[0, 1, 1, 0, 0, 2, 1, 0, 0]
else
[0, 1, 1, 0, 0, 2, 1, 1, 2])
else
(if i.val < 4871 then
[0, 1, 1, 0, 0, 2, 1, 3, 0]
else
[0, 1, 1, 0, 0, 2, 1, 3, 3])))
else
(if i.val < 4876 then
(if i.val < 4874 then
(if i.val < 4873 then
[0, 1, 1, 0, 0, 2, 2, 1, 0]
else
[0, 1, 1, 0, 0, 2, 2, 1, 3])
else
(if i.val < 4875 then
[0, 1, 1, 0, 0, 2, 2, 3, 0]
else
[0, 1, 1, 0, 0, 2, 2, 3, 3]))
else
(if i.val < 4878 then
(if i.val < 4877 then
[0, 1, 1, 0, 0, 2, 3, 0, 0]
else
[0, 1, 1, 0, 0, 2, 3, 0, 1])
else
(if i.val < 4879 then
[0, 1, 1, 0, 0, 2, 3, 3, 2]
else
[0, 1, 1, 0, 0, 3, 0, 1, 2]))))
else
(if i.val < 4888 then
(if i.val < 4884 then
(if i.val < 4882 then
(if i.val < 4881 then
[0, 1, 1, 0, 0, 3, 3, 0, 2]
else
[0, 1, 1, 0, 2, 1, 0, 3, 0])
else
(if i.val < 4883 then
[0, 1, 1, 0, 2, 1, 0, 3, 2]
else
[0, 1, 1, 0, 2, 1, 0, 3, 3]))
else
(if i.val < 4886 then
(if i.val < 4885 then
[0, 1, 1, 0, 2, 1, 1, 0, 3]
else
[0, 1, 1, 0, 2, 1, 1, 2, 3])
else
(if i.val < 4887 then
[0, 1, 1, 0, 2, 1, 1, 3, 2]
else
[0, 1, 1, 0, 2, 1, 3, 0, 1])))
else
(if i.val < 4892 then
(if i.val < 4890 then
(if i.val < 4889 then
[0, 1, 1, 0, 2, 2, 1, 0, 0]
else
[0, 1, 1, 0, 2, 2, 1, 1, 3])
else
(if i.val < 4891 then
[0, 1, 1, 0, 2, 2, 1, 3, 0]
else
[0, 1, 1, 0, 2, 2, 3, 0, 0]))
else
(if i.val < 4894 then
(if i.val < 4893 then
[0, 1, 1, 0, 2, 2, 3, 0, 1]
else
[0, 1, 1, 0, 2, 2, 3, 2, 1])
else
(if i.val < 4895 then
[0, 1, 1, 0, 2, 2, 3, 3, 2]
else
[0, 1, 1, 0, 2, 3, 0, 0, 2])))))
else
(if i.val < 4912 then
(if i.val < 4904 then
(if i.val < 4900 then
(if i.val < 4898 then
(if i.val < 4897 then
[0, 1, 1, 0, 2, 3, 0, 0, 3]
else
[0, 1, 1, 0, 2, 3, 0, 2, 1])
else
(if i.val < 4899 then
[0, 1, 1, 0, 2, 3, 0, 2, 2]
else
[0, 1, 1, 0, 2, 3, 0, 2, 3]))
else
(if i.val < 4902 then
(if i.val < 4901 then
[0, 1, 1, 0, 2, 3, 2, 1, 1]
else
[0, 1, 1, 0, 2, 3, 3, 0, 2])
else
(if i.val < 4903 then
[0, 1, 1, 0, 2, 3, 3, 2, 1]
else
[0, 1, 1, 0, 2, 3, 3, 2, 2])))
else
(if i.val < 4908 then
(if i.val < 4906 then
(if i.val < 4905 then
[0, 1, 1, 0, 3, 0, 0, 2, 1]
else
[0, 1, 1, 0, 3, 0, 0, 2, 2])
else
(if i.val < 4907 then
[0, 1, 1, 0, 3, 0, 0, 3, 2]
else
[0, 1, 1, 0, 3, 0, 1, 2, 1]))
else
(if i.val < 4910 then
(if i.val < 4909 then
[0, 1, 1, 0, 3, 0, 1, 2, 2]
else
[0, 1, 1, 0, 3, 0, 2, 1, 0])
else
(if i.val < 4911 then
[0, 1, 1, 0, 3, 0, 2, 1, 3]
else
[0, 1, 1, 0, 3, 0, 2, 2, 1]))))
else
(if i.val < 4920 then
(if i.val < 4916 then
(if i.val < 4914 then
(if i.val < 4913 then
[0, 1, 1, 0, 3, 0, 2, 2, 3]
else
[0, 1, 1, 0, 3, 2, 1, 1, 0])
else
(if i.val < 4915 then
[0, 1, 1, 0, 3, 2, 1, 1, 2]
else
[0, 1, 1, 0, 3, 2, 2, 1, 0]))
else
(if i.val < 4918 then
(if i.val < 4917 then
[0, 1, 1, 0, 3, 2, 2, 1, 3]
else
[0, 1, 1, 0, 3, 3, 0, 1, 2])
else
(if i.val < 4919 then
[0, 1, 1, 0, 3, 3, 0, 2, 1]
else
[0, 1, 1, 0, 3, 3, 0, 2, 2])))
else
(if i.val < 4924 then
(if i.val < 4922 then
(if i.val < 4921 then
[0, 1, 1, 0, 3, 3, 0, 2, 3]
else
[0, 1, 1, 0, 3, 3, 2, 2, 1])
else
(if i.val < 4923 then
[0, 1, 1, 2, 1, 0, 0, 1, 2]
else
[0, 1, 1, 2, 1, 0, 3, 0, 0]))
else
(if i.val < 4926 then
(if i.val < 4925 then
[0, 1, 1, 2, 1, 0, 3, 0, 1]
else
[0, 1, 1, 2, 1, 0, 3, 0, 2])
else
(if i.val < 4927 then
[0, 1, 1, 2, 1, 0, 3, 3, 2]
else
[0, 1, 1, 2, 1, 1, 0, 2, 1]))))))
else
(if i.val < 4960 then
(if i.val < 4944 then
(if i.val < 4936 then
(if i.val < 4932 then
(if i.val < 4930 then
(if i.val < 4929 then
[0, 1, 1, 2, 1, 1, 0, 3, 2]
else
[0, 1, 1, 2, 1, 1, 0, 3, 3])
else
(if i.val < 4931 then
[0, 1, 1, 2, 1, 1, 2, 3, 2]
else
[0, 1, 1, 2, 1, 1, 2, 3, 3]))
else
(if i.val < 4934 then
(if i.val < 4933 then
[0, 1, 1, 2, 1, 1, 3, 0, 0]
else
[0, 1, 1, 2, 1, 1, 3, 0, 1])
else
(if i.val < 4935 then
[0, 1, 1, 2, 1, 1, 3, 2, 2]
else
[0, 1, 1, 2, 1, 1, 3, 3, 2])))
else
(if i.val < 4940 then
(if i.val < 4938 then
(if i.val < 4937 then
[0, 1, 1, 2, 1, 3, 0, 0, 2]
else
[0, 1, 1, 2, 1, 3, 2, 2, 1])
else
(if i.val < 4939 then
[0, 1, 1, 2, 1, 3, 3, 0, 0]
else
[0, 1, 1, 2, 1, 3, 3, 0, 1]))
else
(if i.val < 4942 then
(if i.val < 4941 then
[0, 1, 1, 2, 1, 3, 3, 2, 2]
else
[0, 1, 1, 2, 2, 1, 0, 0, 3])
else
(if i.val < 4943 then
[0, 1, 1, 2, 2, 1, 0, 3, 0]
else
[0, 1, 1, 2, 2, 1, 0, 3, 2]))))
else
(if i.val < 4952 then
(if i.val < 4948 then
(if i.val < 4946 then
(if i.val < 4945 then
[0, 1, 1, 2, 2, 1, 0, 3, 3]
else
[0, 1, 1, 2, 2, 1, 1, 0, 0])
else
(if i.val < 4947 then
[0, 1, 1, 2, 2, 1, 1, 3, 0]
else
[0, 1, 1, 2, 2, 1, 1, 3, 2]))
else
(if i.val < 4950 then
(if i.val < 4949 then
[0, 1, 1, 2, 2, 1, 1, 3, 3]
else
[0, 1, 1, 2, 2, 1, 3, 0, 0])
else
(if i.val < 4951 then
[0, 1, 1, 2, 2, 1, 3, 0, 2]
else
[0, 1, 1, 2, 2, 1, 3, 3, 2])))
else
(if i.val < 4956 then
(if i.val < 4954 then
(if i.val < 4953 then
[0, 1, 1, 2, 2, 3, 0, 0, 2]
else
[0, 1, 1, 2, 2, 3, 0, 0, 3])
else
(if i.val < 4955 then
[0, 1, 1, 2, 2, 3, 0, 1, 2]
else
[0, 1, 1, 2, 2, 3, 0, 2, 3]))
else
(if i.val < 4958 then
(if i.val < 4957 then
[0, 1, 1, 2, 2, 3, 2, 1, 0]
else
[0, 1, 1, 2, 2, 3, 2, 1, 1])
else
(if i.val < 4959 then
[0, 1, 1, 2, 2, 3, 2, 2, 1]
else
[0, 1, 1, 2, 2, 3, 2, 2, 3])))))
else
(if i.val < 4976 then
(if i.val < 4968 then
(if i.val < 4964 then
(if i.val < 4962 then
(if i.val < 4961 then
[0, 1, 1, 2, 2, 3, 3, 0, 0]
else
[0, 1, 1, 2, 2, 3, 3, 0, 1])
else
(if i.val < 4963 then
[0, 1, 1, 2, 3, 0, 0, 2, 3]
else
[0, 1, 1, 2, 3, 0, 1, 1, 2]))
else
(if i.val < 4966 then
(if i.val < 4965 then
[0, 1, 1, 2, 3, 0, 1, 2, 2]
else
[0, 1, 1, 2, 3, 0, 1, 2, 3])
else
(if i.val < 4967 then
[0, 1, 1, 2, 3, 0, 2, 1, 1]
else
[0, 1, 1, 2, 3, 0, 2, 1, 3])))
else
(if i.val < 4972 then
(if i.val < 4970 then
(if i.val < 4969 then
[0, 1, 1, 2, 3, 0, 2, 2, 1]
else
[0, 1, 1, 2, 3, 2, 1, 0, 0])
else
(if i.val < 4971 then
[0, 1, 1, 2, 3, 2, 1, 0, 3]
else
[0, 1, 1, 2, 3, 2, 1, 1, 0]))
else
(if i.val < 4974 then
(if i.val < 4973 then
[0, 1, 1, 2, 3, 2, 2, 1, 3]
else
[0, 1, 1, 2, 3, 2, 2, 3, 0])
else
(if i.val < 4975 then
[0, 1, 1, 2, 3, 3, 0, 1, 2]
else
[0, 1, 1, 2, 3, 3, 0, 2, 1]))))
else
(if i.val < 4984 then
(if i.val < 4980 then
(if i.val < 4978 then
(if i.val < 4977 then
[0, 1, 1, 2, 3, 3, 0, 2, 2]
else
[0, 1, 1, 2, 3, 3, 0, 2, 3])
else
(if i.val < 4979 then
[0, 1, 1, 3, 0, 0, 1, 1, 2]
else
[0, 1, 1, 3, 0, 0, 1, 2, 1]))
else
(if i.val < 4982 then
(if i.val < 4981 then
[0, 1, 1, 3, 0, 0, 1, 2, 2]
else
[0, 1, 1, 3, 0, 0, 2, 1, 0])
else
(if i.val < 4983 then
[0, 1, 1, 3, 0, 0, 2, 1, 1]
else
[0, 1, 1, 3, 0, 0, 2, 1, 3])))
else
(if i.val < 4988 then
(if i.val < 4986 then
(if i.val < 4985 then
[0, 1, 1, 3, 0, 0, 2, 2, 3]
else
[0, 1, 1, 3, 0, 0, 2, 3, 2])
else
(if i.val < 4987 then
[0, 1, 1, 3, 0, 0, 2, 3, 3]
else
[0, 1, 1, 3, 0, 1, 1, 0, 2]))
else
(if i.val < 4990 then
(if i.val < 4989 then
[0, 1, 1, 3, 0, 1, 1, 2, 1]
else
[0, 1, 1, 3, 0, 1, 1, 2, 2])
else
(if i.val < 4991 then
[0, 1, 1, 3, 0, 1, 1, 2, 3]
else
[0, 1, 1, 3, 0, 1, 2, 1, 1])))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row31_cosetWordsPart0039 : Fin 8640 → List (Fin 4) :=
  fun i => (if i.val < 5056 then
(if i.val < 5024 then
(if i.val < 5008 then
(if i.val < 5000 then
(if i.val < 4996 then
(if i.val < 4994 then
(if i.val < 4993 then
[0, 1, 1, 3, 0, 1, 2, 2, 1]
else
[0, 1, 1, 3, 0, 1, 2, 3, 3])
else
(if i.val < 4995 then
[0, 1, 1, 3, 0, 2, 1, 0, 0]
else
[0, 1, 1, 3, 0, 2, 1, 0, 3]))
else
(if i.val < 4998 then
(if i.val < 4997 then
[0, 1, 1, 3, 0, 2, 1, 1, 2]
else
[0, 1, 1, 3, 0, 2, 2, 1, 0])
else
(if i.val < 4999 then
[0, 1, 1, 3, 0, 2, 2, 1, 1]
else
[0, 1, 1, 3, 0, 2, 2, 1, 3])))
else
(if i.val < 5004 then
(if i.val < 5002 then
(if i.val < 5001 then
[0, 1, 1, 3, 0, 2, 2, 3, 0]
else
[0, 1, 1, 3, 0, 2, 3, 3, 2])
else
(if i.val < 5003 then
[0, 1, 1, 3, 2, 1, 0, 0, 3]
else
[0, 1, 1, 3, 2, 1, 0, 3, 2]))
else
(if i.val < 5006 then
(if i.val < 5005 then
[0, 1, 1, 3, 2, 1, 1, 0, 0]
else
[0, 1, 1, 3, 2, 1, 1, 2, 3])
else
(if i.val < 5007 then
[0, 1, 1, 3, 2, 2, 1, 0, 0]
else
[0, 1, 1, 3, 2, 2, 1, 1, 3]))))
else
(if i.val < 5016 then
(if i.val < 5012 then
(if i.val < 5010 then
(if i.val < 5009 then
[0, 1, 1, 3, 2, 2, 1, 3, 0]
else
[0, 1, 1, 3, 2, 2, 3, 0, 0])
else
(if i.val < 5011 then
[0, 1, 1, 3, 2, 2, 3, 0, 1]
else
[0, 1, 1, 3, 3, 0, 0, 2, 1]))
else
(if i.val < 5014 then
(if i.val < 5013 then
[0, 1, 1, 3, 3, 0, 0, 2, 2]
else
[0, 1, 1, 3, 3, 0, 1, 2, 1])
else
(if i.val < 5015 then
[0, 1, 1, 3, 3, 0, 1, 2, 2]
else
[0, 1, 1, 3, 3, 0, 2, 1, 1])))
else
(if i.val < 5020 then
(if i.val < 5018 then
(if i.val < 5017 then
[0, 1, 1, 3, 3, 0, 2, 2, 1]
else
[0, 1, 1, 3, 3, 2, 1, 0, 0])
else
(if i.val < 5019 then
[0, 1, 1, 3, 3, 2, 1, 0, 3]
else
[0, 1, 2, 1, 0, 0, 1, 2, 3]))
else
(if i.val < 5022 then
(if i.val < 5021 then
[0, 1, 2, 1, 0, 0, 3, 2, 2]
else
[0, 1, 2, 1, 0, 3, 0, 2, 2])
else
(if i.val < 5023 then
[0, 1, 2, 1, 0, 3, 0, 2, 3]
else
[0, 1, 2, 1, 0, 3, 2, 1, 1])))))
else
(if i.val < 5040 then
(if i.val < 5032 then
(if i.val < 5028 then
(if i.val < 5026 then
(if i.val < 5025 then
[0, 1, 2, 1, 0, 3, 2, 2, 3]
else
[0, 1, 2, 1, 0, 3, 3, 0, 1])
else
(if i.val < 5027 then
[0, 1, 2, 1, 0, 3, 3, 2, 1]
else
[0, 1, 2, 1, 1, 0, 0, 2, 3]))
else
(if i.val < 5030 then
(if i.val < 5029 then
[0, 1, 2, 1, 1, 0, 2, 3, 0]
else
[0, 1, 2, 1, 1, 0, 2, 3, 2])
else
(if i.val < 5031 then
[0, 1, 2, 1, 1, 0, 3, 0, 2]
else
[0, 1, 2, 1, 1, 0, 3, 3, 2])))
else
(if i.val < 5036 then
(if i.val < 5034 then
(if i.val < 5033 then
[0, 1, 2, 1, 1, 2, 3, 0, 0]
else
[0, 1, 2, 1, 1, 2, 3, 0, 2])
else
(if i.val < 5035 then
[0, 1, 2, 1, 1, 2, 3, 3, 0]
else
[0, 1, 2, 1, 1, 3, 0, 1, 2]))
else
(if i.val < 5038 then
(if i.val < 5037 then
[0, 1, 2, 1, 1, 3, 0, 2, 1]
else
[0, 1, 2, 1, 1, 3, 0, 2, 2])
else
(if i.val < 5039 then
[0, 1, 2, 1, 1, 3, 0, 2, 3]
else
[0, 1, 2, 1, 1, 3, 2, 1, 1]))))
else
(if i.val < 5048 then
(if i.val < 5044 then
(if i.val < 5042 then
(if i.val < 5041 then
[0, 1, 2, 1, 1, 3, 2, 2, 1]
else
[0, 1, 2, 1, 1, 3, 2, 2, 3])
else
(if i.val < 5043 then
[0, 1, 2, 1, 3, 0, 0, 1, 2]
else
[0, 1, 2, 1, 3, 0, 0, 2, 2]))
else
(if i.val < 5046 then
(if i.val < 5045 then
[0, 1, 2, 1, 3, 0, 1, 2, 1]
else
[0, 1, 2, 1, 3, 0, 1, 2, 2])
else
(if i.val < 5047 then
[0, 1, 2, 1, 3, 0, 1, 2, 3]
else
[0, 1, 2, 1, 3, 0, 2, 1, 1])))
else
(if i.val < 5052 then
(if i.val < 5050 then
(if i.val < 5049 then
[0, 1, 2, 1, 3, 0, 2, 2, 3]
else
[0, 1, 2, 1, 3, 2, 1, 1, 0])
else
(if i.val < 5051 then
[0, 1, 2, 1, 3, 2, 1, 1, 2]
else
[0, 1, 2, 1, 3, 2, 2, 1, 1]))
else
(if i.val < 5054 then
(if i.val < 5053 then
[0, 1, 2, 1, 3, 2, 2, 1, 3]
else
[0, 1, 2, 1, 3, 2, 2, 3, 0])
else
(if i.val < 5055 then
[0, 1, 2, 1, 3, 3, 0, 1, 2]
else
[0, 1, 2, 1, 3, 3, 0, 2, 1]))))))
else
(if i.val < 5088 then
(if i.val < 5072 then
(if i.val < 5064 then
(if i.val < 5060 then
(if i.val < 5058 then
(if i.val < 5057 then
[0, 1, 2, 1, 3, 3, 0, 2, 2]
else
[0, 1, 2, 1, 3, 3, 2, 1, 1])
else
(if i.val < 5059 then
[0, 1, 2, 1, 3, 3, 2, 2, 1]
else
[0, 1, 2, 2, 1, 0, 0, 1, 2]))
else
(if i.val < 5062 then
(if i.val < 5061 then
[0, 1, 2, 2, 1, 0, 0, 1, 3]
else
[0, 1, 2, 2, 1, 0, 3, 0, 0])
else
(if i.val < 5063 then
[0, 1, 2, 2, 1, 0, 3, 0, 1]
else
[0, 1, 2, 2, 1, 0, 3, 0, 2])))
else
(if i.val < 5068 then
(if i.val < 5066 then
(if i.val < 5065 then
[0, 1, 2, 2, 1, 0, 3, 2, 1]
else
[0, 1, 2, 2, 1, 1, 0, 3, 2])
else
(if i.val < 5067 then
[0, 1, 2, 2, 1, 1, 0, 3, 3]
else
[0, 1, 2, 2, 1, 1, 3, 0, 0]))
else
(if i.val < 5070 then
(if i.val < 5069 then
[0, 1, 2, 2, 1, 1, 3, 0, 1]
else
[0, 1, 2, 2, 1, 1, 3, 2, 1])
else
(if i.val < 5071 then
[0, 1, 2, 2, 1, 3, 0, 0, 2]
else
[0, 1, 2, 2, 1, 3, 0, 1, 1]))))
else
(if i.val < 5080 then
(if i.val < 5076 then
(if i.val < 5074 then
(if i.val < 5073 then
[0, 1, 2, 2, 1, 3, 0, 1, 2]
else
[0, 1, 2, 2, 1, 3, 0, 2, 1])
else
(if i.val < 5075 then
[0, 1, 2, 2, 1, 3, 0, 2, 3]
else
[0, 1, 2, 2, 1, 3, 2, 1, 1]))
else
(if i.val < 5078 then
(if i.val < 5077 then
[0, 1, 2, 2, 1, 3, 2, 2, 1]
else
[0, 1, 2, 2, 1, 3, 3, 0, 0])
else
(if i.val < 5079 then
[0, 1, 2, 2, 1, 3, 3, 0, 1]
else
[0, 1, 2, 2, 1, 3, 3, 0, 2])))
else
(if i.val < 5084 then
(if i.val < 5082 then
(if i.val < 5081 then
[0, 1, 2, 2, 1, 3, 3, 2, 1]
else
[0, 1, 2, 2, 3, 0, 0, 3, 2])
else
(if i.val < 5083 then
[0, 1, 2, 2, 3, 0, 2, 2, 1]
else
[0, 1, 2, 2, 3, 2, 2, 1, 1]))
else
(if i.val < 5086 then
(if i.val < 5085 then
[0, 1, 2, 2, 3, 2, 2, 1, 3]
else
[0, 1, 2, 2, 3, 3, 0, 0, 2])
else
(if i.val < 5087 then
[0, 1, 2, 2, 3, 3, 0, 2, 2]
else
[0, 1, 2, 2, 3, 3, 2, 2, 1])))))
else
(if i.val < 5104 then
(if i.val < 5096 then
(if i.val < 5092 then
(if i.val < 5090 then
(if i.val < 5089 then
[0, 1, 2, 3, 0, 0, 1, 1, 2]
else
[0, 1, 2, 3, 0, 0, 1, 2, 1])
else
(if i.val < 5091 then
[0, 1, 2, 3, 0, 0, 1, 2, 3]
else
[0, 1, 2, 3, 0, 0, 2, 1, 1]))
else
(if i.val < 5094 then
(if i.val < 5093 then
[0, 1, 2, 3, 0, 0, 2, 2, 3]
else
[0, 1, 2, 3, 0, 0, 3, 2, 2])
else
(if i.val < 5095 then
[0, 1, 2, 3, 0, 1, 1, 2, 1]
else
[0, 1, 2, 3, 0, 1, 1, 2, 2])))
else
(if i.val < 5100 then
(if i.val < 5098 then
(if i.val < 5097 then
[0, 1, 2, 3, 0, 1, 1, 2, 3]
else
[0, 1, 2, 3, 0, 1, 2, 1, 3])
else
(if i.val < 5099 then
[0, 1, 2, 3, 0, 1, 2, 2, 1]
else
[0, 1, 2, 3, 0, 1, 2, 2, 3]))
else
(if i.val < 5102 then
(if i.val < 5101 then
[0, 1, 2, 3, 0, 1, 2, 3, 0]
else
[0, 1, 2, 3, 0, 1, 2, 3, 3])
else
(if i.val < 5103 then
[0, 1, 2, 3, 0, 2, 1, 1, 2]
else
[0, 1, 2, 3, 0, 2, 1, 3, 2]))))
else
(if i.val < 5112 then
(if i.val < 5108 then
(if i.val < 5106 then
(if i.val < 5105 then
[0, 1, 2, 3, 0, 2, 2, 1, 1]
else
[0, 1, 2, 3, 0, 2, 2, 1, 3])
else
(if i.val < 5107 then
[0, 1, 2, 3, 0, 2, 2, 3, 0]
else
[0, 1, 2, 3, 2, 1, 0, 3, 2]))
else
(if i.val < 5110 then
(if i.val < 5109 then
[0, 1, 2, 3, 2, 1, 1, 2, 3]
else
[0, 1, 2, 3, 2, 2, 1, 0, 0])
else
(if i.val < 5111 then
[0, 1, 2, 3, 2, 2, 1, 0, 3]
else
[0, 1, 2, 3, 2, 2, 1, 1, 0])))
else
(if i.val < 5116 then
(if i.val < 5114 then
(if i.val < 5113 then
[0, 1, 2, 3, 2, 2, 1, 1, 3]
else
[0, 1, 2, 3, 2, 2, 1, 3, 0])
else
(if i.val < 5115 then
[0, 1, 2, 3, 3, 0, 0, 2, 1]
else
[0, 1, 2, 3, 3, 0, 0, 2, 2]))
else
(if i.val < 5118 then
(if i.val < 5117 then
[0, 1, 2, 3, 3, 0, 0, 2, 3]
else
[0, 1, 2, 3, 3, 0, 1, 1, 2])
else
(if i.val < 5119 then
[0, 1, 2, 3, 3, 0, 1, 2, 1]
else
[0, 1, 2, 3, 3, 0, 1, 2, 2])))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row31_cosetWordsPart0040 : Fin 8640 → List (Fin 4) :=
  fun i => (if i.val < 5184 then
(if i.val < 5152 then
(if i.val < 5136 then
(if i.val < 5128 then
(if i.val < 5124 then
(if i.val < 5122 then
(if i.val < 5121 then
[0, 1, 2, 3, 3, 0, 1, 2, 3]
else
[0, 1, 2, 3, 3, 0, 2, 2, 1])
else
(if i.val < 5123 then
[0, 1, 2, 3, 3, 0, 2, 2, 3]
else
[0, 1, 2, 3, 3, 0, 2, 3, 3]))
else
(if i.val < 5126 then
(if i.val < 5125 then
[0, 1, 2, 3, 3, 2, 1, 0, 0]
else
[0, 1, 2, 3, 3, 2, 1, 0, 3])
else
(if i.val < 5127 then
[0, 1, 2, 3, 3, 2, 2, 1, 1]
else
[0, 1, 3, 0, 0, 1, 1, 2, 1])))
else
(if i.val < 5132 then
(if i.val < 5130 then
(if i.val < 5129 then
[0, 1, 3, 0, 0, 1, 1, 2, 2]
else
[0, 1, 3, 0, 0, 1, 1, 2, 3])
else
(if i.val < 5131 then
[0, 1, 3, 0, 0, 1, 2, 1, 1]
else
[0, 1, 3, 0, 0, 1, 2, 1, 3]))
else
(if i.val < 5134 then
(if i.val < 5133 then
[0, 1, 3, 0, 0, 1, 2, 2, 3]
else
[0, 1, 3, 0, 0, 1, 2, 3, 2])
else
(if i.val < 5135 then
[0, 1, 3, 0, 0, 1, 2, 3, 3]
else
[0, 1, 3, 0, 0, 2, 1, 1, 2]))))
else
(if i.val < 5144 then
(if i.val < 5140 then
(if i.val < 5138 then
(if i.val < 5137 then
[0, 1, 3, 0, 0, 2, 2, 3, 2]
else
[0, 1, 3, 0, 0, 2, 2, 3, 3])
else
(if i.val < 5139 then
[0, 1, 3, 0, 0, 2, 3, 2, 1]
else
[0, 1, 3, 0, 0, 3, 2, 1, 1]))
else
(if i.val < 5142 then
(if i.val < 5141 then
[0, 1, 3, 0, 0, 3, 2, 2, 1]
else
[0, 1, 3, 0, 1, 1, 2, 2, 1])
else
(if i.val < 5143 then
[0, 1, 3, 0, 1, 1, 2, 2, 3]
else
[0, 1, 3, 0, 1, 2, 1, 0, 0])))
else
(if i.val < 5148 then
(if i.val < 5146 then
(if i.val < 5145 then
[0, 1, 3, 0, 1, 2, 1, 1, 0]
else
[0, 1, 3, 0, 1, 2, 1, 1, 2])
else
(if i.val < 5147 then
[0, 1, 3, 0, 1, 2, 1, 3, 0]
else
[0, 1, 3, 0, 1, 2, 2, 1, 0]))
else
(if i.val < 5150 then
(if i.val < 5149 then
[0, 1, 3, 0, 1, 2, 2, 1, 1]
else
[0, 1, 3, 0, 1, 2, 2, 1, 3])
else
(if i.val < 5151 then
[0, 1, 3, 0, 1, 2, 2, 3, 0]
else
[0, 1, 3, 0, 1, 2, 3, 3, 0])))))
else
(if i.val < 5168 then
(if i.val < 5160 then
(if i.val < 5156 then
(if i.val < 5154 then
(if i.val < 5153 then
[0, 1, 3, 0, 2, 1, 1, 3, 2]
else
[0, 1, 3, 0, 2, 2, 1, 0, 0])
else
(if i.val < 5155 then
[0, 1, 3, 0, 2, 3, 3, 0, 2]
else
[0, 1, 3, 2, 1, 0, 3, 2, 1]))
else
(if i.val < 5158 then
(if i.val < 5157 then
[0, 1, 3, 2, 1, 0, 3, 2, 2]
else
[0, 1, 3, 2, 1, 1, 0, 0, 2])
else
(if i.val < 5159 then
[0, 1, 3, 2, 1, 1, 0, 2, 3]
else
[0, 1, 3, 2, 1, 1, 2, 3, 3])))
else
(if i.val < 5164 then
(if i.val < 5162 then
(if i.val < 5161 then
[0, 1, 3, 2, 2, 1, 0, 3, 2]
else
[0, 1, 3, 2, 2, 1, 1, 3, 2])
else
(if i.val < 5163 then
[0, 1, 3, 2, 2, 3, 0, 1, 1]
else
[0, 1, 3, 2, 2, 3, 0, 1, 2]))
else
(if i.val < 5166 then
(if i.val < 5165 then
[0, 1, 3, 3, 0, 0, 1, 1, 2]
else
[0, 1, 3, 3, 0, 0, 1, 2, 3])
else
(if i.val < 5167 then
[0, 1, 3, 3, 0, 0, 2, 1, 0]
else
[0, 1, 3, 3, 0, 0, 2, 1, 1]))))
else
(if i.val < 5176 then
(if i.val < 5172 then
(if i.val < 5170 then
(if i.val < 5169 then
[0, 1, 3, 3, 0, 0, 2, 1, 3]
else
[0, 1, 3, 3, 0, 0, 2, 2, 1])
else
(if i.val < 5171 then
[0, 1, 3, 3, 0, 0, 2, 2, 3]
else
[0, 1, 3, 3, 0, 0, 2, 3, 3]))
else
(if i.val < 5174 then
(if i.val < 5173 then
[0, 1, 3, 3, 0, 1, 2, 1, 0]
else
[0, 1, 3, 3, 0, 1, 2, 1, 3])
else
(if i.val < 5175 then
[0, 1, 3, 3, 0, 1, 2, 2, 1]
else
[0, 1, 3, 3, 0, 1, 2, 2, 3])))
else
(if i.val < 5180 then
(if i.val < 5178 then
(if i.val < 5177 then
[0, 1, 3, 3, 0, 1, 2, 3, 0]
else
[0, 1, 3, 3, 0, 2, 1, 0, 0])
else
(if i.val < 5179 then
[0, 1, 3, 3, 0, 2, 1, 0, 3]
else
[0, 1, 3, 3, 0, 2, 1, 1, 2]))
else
(if i.val < 5182 then
(if i.val < 5181 then
[0, 1, 3, 3, 0, 2, 2, 1, 0]
else
[0, 1, 3, 3, 0, 2, 2, 1, 1])
else
(if i.val < 5183 then
[0, 1, 3, 3, 0, 2, 2, 1, 3]
else
[0, 1, 3, 3, 0, 2, 3, 3, 0]))))))
else
(if i.val < 5216 then
(if i.val < 5200 then
(if i.val < 5192 then
(if i.val < 5188 then
(if i.val < 5186 then
(if i.val < 5185 then
[0, 1, 3, 3, 0, 2, 3, 3, 2]
else
[0, 1, 3, 3, 2, 1, 0, 0, 3])
else
(if i.val < 5187 then
[0, 1, 3, 3, 2, 1, 0, 3, 3]
else
[0, 1, 3, 3, 2, 1, 1, 0, 0]))
else
(if i.val < 5190 then
(if i.val < 5189 then
[0, 1, 3, 3, 2, 1, 1, 2, 3]
else
[0, 2, 1, 0, 0, 1, 2, 2, 1])
else
(if i.val < 5191 then
[0, 2, 1, 0, 0, 1, 2, 2, 3]
else
[0, 2, 1, 0, 0, 1, 2, 3, 0])))
else
(if i.val < 5196 then
(if i.val < 5194 then
(if i.val < 5193 then
[0, 2, 1, 0, 0, 1, 2, 3, 3]
else
[0, 2, 1, 0, 0, 1, 3, 0, 2])
else
(if i.val < 5195 then
[0, 2, 1, 0, 0, 1, 3, 2, 2]
else
[0, 2, 1, 0, 0, 3, 2, 2, 1]))
else
(if i.val < 5198 then
(if i.val < 5197 then
[0, 2, 1, 0, 0, 3, 3, 2, 1]
else
[0, 2, 1, 0, 0, 3, 3, 2, 2])
else
(if i.val < 5199 then
[0, 2, 1, 0, 3, 0, 0, 1, 2]
else
[0, 2, 1, 0, 3, 0, 0, 2, 1]))))
else
(if i.val < 5208 then
(if i.val < 5204 then
(if i.val < 5202 then
(if i.val < 5201 then
[0, 2, 1, 0, 3, 0, 0, 2, 2]
else
[0, 2, 1, 0, 3, 0, 0, 3, 2])
else
(if i.val < 5203 then
[0, 2, 1, 0, 3, 0, 1, 2, 1]
else
[0, 2, 1, 0, 3, 0, 2, 1, 0]))
else
(if i.val < 5206 then
(if i.val < 5205 then
[0, 2, 1, 0, 3, 0, 2, 1, 1]
else
[0, 2, 1, 0, 3, 0, 2, 1, 3])
else
(if i.val < 5207 then
[0, 2, 1, 0, 3, 0, 2, 2, 1]
else
[0, 2, 1, 0, 3, 0, 2, 2, 3])))
else
(if i.val < 5212 then
(if i.val < 5210 then
(if i.val < 5209 then
[0, 2, 1, 0, 3, 2, 1, 1, 0]
else
[0, 2, 1, 0, 3, 2, 2, 1, 0])
else
(if i.val < 5211 then
[0, 2, 1, 0, 3, 3, 0, 1, 2]
else
[0, 2, 1, 0, 3, 3, 0, 2, 1]))
else
(if i.val < 5214 then
(if i.val < 5213 then
[0, 2, 1, 0, 3, 3, 0, 2, 2]
else
[0, 2, 1, 0, 3, 3, 2, 1, 0])
else
(if i.val < 5215 then
[0, 2, 1, 0, 3, 3, 2, 1, 1]
else
[0, 2, 1, 0, 3, 3, 2, 2, 1])))))
else
(if i.val < 5232 then
(if i.val < 5224 then
(if i.val < 5220 then
(if i.val < 5218 then
(if i.val < 5217 then
[0, 2, 1, 1, 0, 0, 2, 1, 3]
else
[0, 2, 1, 1, 0, 0, 2, 3, 0])
else
(if i.val < 5219 then
[0, 2, 1, 1, 0, 0, 2, 3, 3]
else
[0, 2, 1, 1, 0, 2, 1, 1, 2]))
else
(if i.val < 5222 then
(if i.val < 5221 then
[0, 2, 1, 1, 0, 2, 1, 1, 3]
else
[0, 2, 1, 1, 0, 2, 1, 3, 0])
else
(if i.val < 5223 then
[0, 2, 1, 1, 0, 2, 1, 3, 2]
else
[0, 2, 1, 1, 0, 2, 3, 0, 0])))
else
(if i.val < 5228 then
(if i.val < 5226 then
(if i.val < 5225 then
[0, 2, 1, 1, 0, 2, 3, 0, 1]
else
[0, 2, 1, 1, 0, 2, 3, 0, 2])
else
(if i.val < 5227 then
[0, 2, 1, 1, 0, 2, 3, 2, 1]
else
[0, 2, 1, 1, 0, 2, 3, 3, 2]))
else
(if i.val < 5230 then
(if i.val < 5229 then
[0, 2, 1, 1, 0, 3, 0, 0, 2]
else
[0, 2, 1, 1, 0, 3, 0, 2, 1])
else
(if i.val < 5231 then
[0, 2, 1, 1, 0, 3, 0, 2, 2]
else
[0, 2, 1, 1, 0, 3, 0, 2, 3]))))
else
(if i.val < 5240 then
(if i.val < 5236 then
(if i.val < 5234 then
(if i.val < 5233 then
[0, 2, 1, 1, 0, 3, 2, 1, 0]
else
[0, 2, 1, 1, 0, 3, 2, 1, 1])
else
(if i.val < 5235 then
[0, 2, 1, 1, 0, 3, 2, 2, 3]
else
[0, 2, 1, 1, 2, 3, 0, 0, 3]))
else
(if i.val < 5238 then
(if i.val < 5237 then
[0, 2, 1, 1, 2, 3, 0, 2, 1]
else
[0, 2, 1, 1, 2, 3, 0, 2, 2])
else
(if i.val < 5239 then
[0, 2, 1, 1, 2, 3, 2, 1, 0]
else
[0, 2, 1, 1, 2, 3, 2, 1, 1])))
else
(if i.val < 5244 then
(if i.val < 5242 then
(if i.val < 5241 then
[0, 2, 1, 1, 2, 3, 3, 0, 0]
else
[0, 2, 1, 1, 2, 3, 3, 0, 1])
else
(if i.val < 5243 then
[0, 2, 1, 1, 2, 3, 3, 2, 1]
else
[0, 2, 1, 1, 3, 0, 0, 2, 2]))
else
(if i.val < 5246 then
(if i.val < 5245 then
[0, 2, 1, 1, 3, 0, 1, 1, 2]
else
[0, 2, 1, 1, 3, 0, 1, 2, 1])
else
(if i.val < 5247 then
[0, 2, 1, 1, 3, 0, 1, 2, 2]
else
[0, 2, 1, 1, 3, 0, 2, 1, 0])))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row31_cosetWordsPart0041 : Fin 8640 → List (Fin 4) :=
  fun i => (if i.val < 5312 then
(if i.val < 5280 then
(if i.val < 5264 then
(if i.val < 5256 then
(if i.val < 5252 then
(if i.val < 5250 then
(if i.val < 5249 then
[0, 2, 1, 1, 3, 0, 2, 2, 3]
else
[0, 2, 1, 1, 3, 2, 1, 0, 0])
else
(if i.val < 5251 then
[0, 2, 1, 1, 3, 2, 2, 1, 0]
else
[0, 2, 1, 1, 3, 2, 2, 1, 1]))
else
(if i.val < 5254 then
(if i.val < 5253 then
[0, 2, 1, 1, 3, 2, 2, 1, 3]
else
[0, 2, 1, 1, 3, 2, 2, 3, 0])
else
(if i.val < 5255 then
[0, 2, 1, 1, 3, 3, 0, 1, 2]
else
[0, 2, 1, 3, 0, 0, 1, 2, 2])))
else
(if i.val < 5260 then
(if i.val < 5258 then
(if i.val < 5257 then
[0, 2, 1, 3, 0, 0, 3, 2, 2]
else
[0, 2, 1, 3, 0, 1, 2, 1, 0])
else
(if i.val < 5259 then
[0, 2, 1, 3, 0, 1, 2, 1, 1]
else
[0, 2, 1, 3, 0, 1, 2, 2, 1]))
else
(if i.val < 5262 then
(if i.val < 5261 then
[0, 2, 1, 3, 0, 1, 2, 2, 3]
else
[0, 2, 1, 3, 0, 1, 2, 3, 0])
else
(if i.val < 5263 then
[0, 2, 1, 3, 0, 1, 2, 3, 3]
else
[0, 2, 1, 3, 2, 1, 0, 3, 2]))))
else
(if i.val < 5272 then
(if i.val < 5268 then
(if i.val < 5266 then
(if i.val < 5265 then
[0, 2, 1, 3, 2, 1, 1, 0, 0]
else
[0, 2, 1, 3, 2, 1, 1, 2, 3])
else
(if i.val < 5267 then
[0, 2, 1, 3, 2, 2, 1, 1, 3]
else
[0, 2, 1, 3, 3, 0, 0, 2, 2]))
else
(if i.val < 5270 then
(if i.val < 5269 then
[0, 2, 1, 3, 3, 0, 0, 2, 3]
else
[0, 2, 1, 3, 3, 0, 1, 2, 1])
else
(if i.val < 5271 then
[0, 2, 1, 3, 3, 0, 1, 2, 3]
else
[0, 2, 1, 3, 3, 0, 2, 1, 0])))
else
(if i.val < 5276 then
(if i.val < 5274 then
(if i.val < 5273 then
[0, 2, 1, 3, 3, 0, 2, 1, 1]
else
[0, 2, 1, 3, 3, 0, 2, 2, 1])
else
(if i.val < 5275 then
[0, 2, 1, 3, 3, 0, 2, 2, 3]
else
[0, 2, 1, 3, 3, 2, 1, 0, 0]))
else
(if i.val < 5278 then
(if i.val < 5277 then
[0, 2, 1, 3, 3, 2, 1, 0, 3]
else
[0, 2, 1, 3, 3, 2, 1, 1, 0])
else
(if i.val < 5279 then
[0, 2, 1, 3, 3, 2, 2, 1, 1]
else
[0, 2, 2, 1, 0, 0, 1, 2, 3])))))
else
(if i.val < 5296 then
(if i.val < 5288 then
(if i.val < 5284 then
(if i.val < 5282 then
(if i.val < 5281 then
[0, 2, 2, 1, 0, 0, 1, 3, 2]
else
[0, 2, 2, 1, 0, 0, 3, 2, 2])
else
(if i.val < 5283 then
[0, 2, 2, 1, 0, 0, 3, 3, 2]
else
[0, 2, 2, 1, 0, 3, 0, 2, 1]))
else
(if i.val < 5286 then
(if i.val < 5285 then
[0, 2, 2, 1, 0, 3, 0, 2, 3]
else
[0, 2, 2, 1, 0, 3, 2, 1, 0])
else
(if i.val < 5287 then
[0, 2, 2, 1, 0, 3, 2, 1, 1]
else
[0, 2, 2, 1, 0, 3, 3, 0, 1])))
else
(if i.val < 5292 then
(if i.val < 5290 then
(if i.val < 5289 then
[0, 2, 2, 1, 1, 0, 3, 0, 2]
else
[0, 2, 2, 1, 1, 0, 3, 2, 1])
else
(if i.val < 5291 then
[0, 2, 2, 1, 1, 0, 3, 3, 2]
else
[0, 2, 2, 1, 1, 3, 0, 2, 1]))
else
(if i.val < 5294 then
(if i.val < 5293 then
[0, 2, 2, 1, 1, 3, 0, 2, 3]
else
[0, 2, 2, 1, 1, 3, 2, 1, 0])
else
(if i.val < 5295 then
[0, 2, 2, 1, 1, 3, 2, 1, 1]
else
[0, 2, 2, 1, 1, 3, 2, 2, 3]))))
else
(if i.val < 5304 then
(if i.val < 5300 then
(if i.val < 5298 then
(if i.val < 5297 then
[0, 2, 2, 1, 3, 0, 0, 3, 2]
else
[0, 2, 2, 1, 3, 0, 1, 2, 1])
else
(if i.val < 5299 then
[0, 2, 2, 1, 3, 0, 1, 2, 3]
else
[0, 2, 2, 1, 3, 0, 2, 1, 1]))
else
(if i.val < 5302 then
(if i.val < 5301 then
[0, 2, 2, 1, 3, 2, 1, 1, 0]
else
[0, 2, 2, 1, 3, 3, 0, 1, 2])
else
(if i.val < 5303 then
[0, 2, 2, 1, 3, 3, 0, 2, 3]
else
[0, 2, 2, 1, 3, 3, 2, 1, 0])))
else
(if i.val < 5308 then
(if i.val < 5306 then
(if i.val < 5305 then
[0, 2, 2, 1, 3, 3, 2, 1, 1]
else
[0, 2, 2, 3, 0, 0, 1, 1, 2])
else
(if i.val < 5307 then
[0, 2, 2, 3, 0, 0, 2, 1, 0]
else
[0, 2, 2, 3, 0, 0, 2, 1, 1]))
else
(if i.val < 5310 then
(if i.val < 5309 then
[0, 2, 2, 3, 0, 0, 2, 2, 3]
else
[0, 2, 2, 3, 0, 0, 3, 2, 1])
else
(if i.val < 5311 then
[0, 2, 2, 3, 0, 1, 2, 1, 0]
else
[0, 2, 2, 3, 0, 1, 2, 3, 0]))))))
else
(if i.val < 5344 then
(if i.val < 5328 then
(if i.val < 5320 then
(if i.val < 5316 then
(if i.val < 5314 then
(if i.val < 5313 then
[0, 2, 2, 3, 0, 1, 2, 3, 3]
else
[0, 2, 2, 3, 0, 2, 1, 1, 2])
else
(if i.val < 5315 then
[0, 2, 2, 3, 0, 2, 1, 1, 3]
else
[0, 2, 2, 3, 0, 2, 2, 1, 3]))
else
(if i.val < 5318 then
(if i.val < 5317 then
[0, 2, 2, 3, 0, 2, 2, 3, 0]
else
[0, 2, 2, 3, 0, 2, 2, 3, 3])
else
(if i.val < 5319 then
[0, 2, 2, 3, 0, 2, 3, 3, 0]
else
[0, 2, 2, 3, 0, 2, 3, 3, 2])))
else
(if i.val < 5324 then
(if i.val < 5322 then
(if i.val < 5321 then
[0, 2, 2, 3, 2, 2, 1, 0, 0]
else
[0, 2, 2, 3, 2, 2, 1, 0, 3])
else
(if i.val < 5323 then
[0, 2, 2, 3, 2, 2, 1, 1, 3]
else
[0, 2, 2, 3, 2, 2, 3, 0, 0]))
else
(if i.val < 5326 then
(if i.val < 5325 then
[0, 2, 2, 3, 2, 2, 3, 0, 1]
else
[0, 2, 2, 3, 3, 0, 0, 2, 2])
else
(if i.val < 5327 then
[0, 2, 2, 3, 3, 0, 1, 2, 1]
else
[0, 2, 2, 3, 3, 0, 1, 2, 3]))))
else
(if i.val < 5336 then
(if i.val < 5332 then
(if i.val < 5330 then
(if i.val < 5329 then
[0, 2, 2, 3, 3, 0, 2, 1, 0]
else
[0, 2, 2, 3, 3, 0, 2, 1, 1])
else
(if i.val < 5331 then
[0, 2, 2, 3, 3, 0, 2, 2, 3]
else
[0, 2, 2, 3, 3, 0, 2, 3, 3]))
else
(if i.val < 5334 then
(if i.val < 5333 then
[0, 2, 2, 3, 3, 2, 1, 0, 0]
else
[0, 2, 2, 3, 3, 2, 1, 0, 3])
else
(if i.val < 5335 then
[0, 2, 3, 0, 0, 1, 1, 2, 3]
else
[0, 2, 3, 0, 0, 1, 2, 2, 1])))
else
(if i.val < 5340 then
(if i.val < 5338 then
(if i.val < 5337 then
[0, 2, 3, 0, 0, 1, 3, 2, 2]
else
[0, 2, 3, 0, 0, 2, 1, 1, 0])
else
(if i.val < 5339 then
[0, 2, 3, 0, 0, 2, 1, 1, 2]
else
[0, 2, 3, 0, 0, 2, 2, 3, 0]))
else
(if i.val < 5342 then
(if i.val < 5341 then
[0, 2, 3, 0, 0, 2, 3, 2, 1]
else
[0, 2, 3, 0, 0, 2, 3, 3, 2])
else
(if i.val < 5343 then
[0, 2, 3, 0, 0, 3, 2, 1, 0]
else
[0, 2, 3, 0, 0, 3, 2, 1, 1])))))
else
(if i.val < 5360 then
(if i.val < 5352 then
(if i.val < 5348 then
(if i.val < 5346 then
(if i.val < 5345 then
[0, 2, 3, 0, 0, 3, 2, 2, 1]
else
[0, 2, 3, 0, 1, 1, 0, 2, 1])
else
(if i.val < 5347 then
[0, 2, 3, 0, 1, 1, 0, 3, 2]
else
[0, 2, 3, 0, 1, 1, 2, 1, 0]))
else
(if i.val < 5350 then
(if i.val < 5349 then
[0, 2, 3, 0, 1, 1, 2, 1, 1]
else
[0, 2, 3, 0, 1, 1, 2, 2, 3])
else
(if i.val < 5351 then
[0, 2, 3, 0, 1, 1, 2, 3, 0]
else
[0, 2, 3, 0, 1, 1, 2, 3, 3])))
else
(if i.val < 5356 then
(if i.val < 5354 then
(if i.val < 5353 then
[0, 2, 3, 0, 1, 2, 1, 1, 0]
else
[0, 2, 3, 0, 1, 2, 1, 1, 2])
else
(if i.val < 5355 then
[0, 2, 3, 0, 1, 2, 1, 3, 2]
else
[0, 2, 3, 0, 1, 2, 2, 1, 1]))
else
(if i.val < 5358 then
(if i.val < 5357 then
[0, 2, 3, 0, 1, 2, 2, 3, 0]
else
[0, 2, 3, 0, 1, 2, 2, 3, 3])
else
(if i.val < 5359 then
[0, 2, 3, 0, 1, 2, 3, 0, 1]
else
[0, 2, 3, 0, 1, 2, 3, 3, 0]))))
else
(if i.val < 5368 then
(if i.val < 5364 then
(if i.val < 5362 then
(if i.val < 5361 then
[0, 2, 3, 0, 1, 2, 3, 3, 2]
else
[0, 2, 3, 0, 2, 1, 0, 3, 0])
else
(if i.val < 5363 then
[0, 2, 3, 0, 2, 1, 1, 0, 2]
else
[0, 2, 3, 0, 2, 1, 1, 3, 2]))
else
(if i.val < 5366 then
(if i.val < 5365 then
[0, 2, 3, 0, 2, 1, 3, 0, 0]
else
[0, 2, 3, 0, 2, 1, 3, 3, 0])
else
(if i.val < 5367 then
[0, 2, 3, 0, 2, 1, 3, 3, 2]
else
[0, 2, 3, 0, 2, 2, 1, 0, 0])))
else
(if i.val < 5372 then
(if i.val < 5370 then
(if i.val < 5369 then
[0, 2, 3, 0, 2, 2, 1, 0, 3]
else
[0, 2, 3, 0, 2, 2, 1, 3, 0])
else
(if i.val < 5371 then
[0, 2, 3, 0, 2, 2, 1, 3, 3]
else
[0, 2, 3, 0, 2, 2, 3, 3, 0]))
else
(if i.val < 5374 then
(if i.val < 5373 then
[0, 2, 3, 0, 2, 3, 3, 0, 2]
else
[0, 2, 3, 0, 2, 3, 3, 2, 1])
else
(if i.val < 5375 then
[0, 2, 3, 2, 1, 0, 0, 1, 2]
else
[0, 2, 3, 2, 1, 0, 3, 2, 1])))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row31_cosetWordsPart0042 : Fin 8640 → List (Fin 4) :=
  fun i => (if i.val < 5440 then
(if i.val < 5408 then
(if i.val < 5392 then
(if i.val < 5384 then
(if i.val < 5380 then
(if i.val < 5378 then
(if i.val < 5377 then
[0, 2, 3, 2, 1, 0, 3, 2, 2]
else
[0, 2, 3, 2, 1, 1, 0, 3, 2])
else
(if i.val < 5379 then
[0, 2, 3, 2, 1, 1, 0, 3, 3]
else
[0, 2, 3, 2, 2, 1, 0, 3, 0]))
else
(if i.val < 5382 then
(if i.val < 5381 then
[0, 2, 3, 2, 2, 1, 1, 0, 0]
else
[0, 2, 3, 2, 2, 1, 1, 0, 3])
else
(if i.val < 5383 then
[0, 2, 3, 2, 2, 1, 3, 0, 0]
else
[0, 2, 3, 2, 2, 1, 3, 0, 1])))
else
(if i.val < 5388 then
(if i.val < 5386 then
(if i.val < 5385 then
[0, 2, 3, 2, 2, 1, 3, 2, 2]
else
[0, 2, 3, 2, 2, 3, 0, 1, 2])
else
(if i.val < 5387 then
[0, 2, 3, 3, 0, 0, 2, 1, 3]
else
[0, 2, 3, 3, 0, 0, 2, 3, 3]))
else
(if i.val < 5390 then
(if i.val < 5389 then
[0, 2, 3, 3, 0, 1, 1, 0, 2]
else
[0, 2, 3, 3, 0, 1, 2, 1, 1])
else
(if i.val < 5391 then
[0, 2, 3, 3, 0, 1, 2, 1, 3]
else
[0, 2, 3, 3, 0, 1, 2, 3, 0]))))
else
(if i.val < 5400 then
(if i.val < 5396 then
(if i.val < 5394 then
(if i.val < 5393 then
[0, 2, 3, 3, 0, 1, 2, 3, 3]
else
[0, 2, 3, 3, 0, 2, 1, 0, 0])
else
(if i.val < 5395 then
[0, 2, 3, 3, 0, 2, 1, 3, 0]
else
[0, 2, 3, 3, 0, 2, 1, 3, 2]))
else
(if i.val < 5398 then
(if i.val < 5397 then
[0, 2, 3, 3, 0, 2, 2, 1, 3]
else
[0, 2, 3, 3, 0, 2, 2, 3, 3])
else
(if i.val < 5399 then
[0, 2, 3, 3, 0, 2, 3, 3, 2]
else
[0, 2, 3, 3, 2, 1, 0, 0, 3])))
else
(if i.val < 5404 then
(if i.val < 5402 then
(if i.val < 5401 then
[0, 2, 3, 3, 2, 2, 1, 0, 0]
else
[0, 2, 3, 3, 2, 2, 1, 0, 3])
else
(if i.val < 5403 then
[0, 2, 3, 3, 2, 2, 1, 1, 0]
else
[0, 3, 0, 0, 1, 1, 2, 1, 0]))
else
(if i.val < 5406 then
(if i.val < 5405 then
[0, 3, 0, 0, 1, 1, 2, 1, 1]
else
[0, 3, 0, 0, 1, 1, 2, 1, 3])
else
(if i.val < 5407 then
[0, 3, 0, 0, 1, 1, 2, 2, 1]
else
[0, 3, 0, 0, 1, 1, 2, 2, 3])))))
else
(if i.val < 5424 then
(if i.val < 5416 then
(if i.val < 5412 then
(if i.val < 5410 then
(if i.val < 5409 then
[0, 3, 0, 0, 1, 1, 2, 3, 0]
else
[0, 3, 0, 0, 1, 1, 2, 3, 2])
else
(if i.val < 5411 then
[0, 3, 0, 0, 1, 1, 2, 3, 3]
else
[0, 3, 0, 0, 1, 2, 2, 1, 1]))
else
(if i.val < 5414 then
(if i.val < 5413 then
[0, 3, 0, 0, 1, 2, 2, 3, 3]
else
[0, 3, 0, 0, 1, 2, 3, 0, 2])
else
(if i.val < 5415 then
[0, 3, 0, 0, 1, 2, 3, 2, 1]
else
[0, 3, 0, 0, 1, 2, 3, 3, 2])))
else
(if i.val < 5420 then
(if i.val < 5418 then
(if i.val < 5417 then
[0, 3, 0, 0, 1, 3, 0, 0, 2]
else
[0, 3, 0, 0, 1, 3, 2, 2, 1])
else
(if i.val < 5419 then
[0, 3, 0, 0, 2, 1, 0, 3, 2]
else
[0, 3, 0, 0, 2, 1, 1, 0, 2]))
else
(if i.val < 5422 then
(if i.val < 5421 then
[0, 3, 0, 0, 2, 1, 1, 2, 3]
else
[0, 3, 0, 0, 2, 1, 1, 3, 2])
else
(if i.val < 5423 then
[0, 3, 0, 0, 2, 1, 3, 0, 0]
else
[0, 3, 0, 0, 2, 2, 1, 0, 0]))))
else
(if i.val < 5432 then
(if i.val < 5428 then
(if i.val < 5426 then
(if i.val < 5425 then
[0, 3, 0, 0, 2, 2, 1, 0, 3]
else
[0, 3, 0, 0, 2, 2, 1, 3, 0])
else
(if i.val < 5427 then
[0, 3, 0, 0, 2, 2, 1, 3, 2]
else
[0, 3, 0, 0, 2, 2, 3, 0, 0]))
else
(if i.val < 5430 then
(if i.val < 5429 then
[0, 3, 0, 0, 2, 2, 3, 0, 1]
else
[0, 3, 0, 0, 2, 2, 3, 2, 2])
else
(if i.val < 5431 then
[0, 3, 0, 0, 2, 3, 2, 1, 0]
else
[0, 3, 0, 0, 2, 3, 3, 2, 1])))
else
(if i.val < 5436 then
(if i.val < 5434 then
(if i.val < 5433 then
[0, 3, 0, 0, 3, 2, 1, 0, 0]
else
[0, 3, 0, 0, 3, 2, 1, 1, 0])
else
(if i.val < 5435 then
[0, 3, 0, 0, 3, 2, 1, 1, 2]
else
[0, 3, 0, 0, 3, 2, 2, 1, 0]))
else
(if i.val < 5438 then
(if i.val < 5437 then
[0, 3, 0, 0, 3, 2, 2, 1, 1]
else
[0, 3, 0, 0, 3, 2, 2, 1, 3])
else
(if i.val < 5439 then
[0, 3, 0, 0, 3, 2, 2, 3, 0]
else
[0, 3, 0, 1, 1, 0, 2, 1, 0]))))))
else
(if i.val < 5472 then
(if i.val < 5456 then
(if i.val < 5448 then
(if i.val < 5444 then
(if i.val < 5442 then
(if i.val < 5441 then
[0, 3, 0, 1, 1, 0, 2, 2, 1]
else
[0, 3, 0, 1, 1, 0, 2, 3, 2])
else
(if i.val < 5443 then
[0, 3, 0, 1, 1, 0, 2, 3, 3]
else
[0, 3, 0, 1, 1, 0, 3, 2, 1]))
else
(if i.val < 5446 then
(if i.val < 5445 then
[0, 3, 0, 1, 1, 2, 1, 0, 3]
else
[0, 3, 0, 1, 1, 2, 1, 1, 0])
else
(if i.val < 5447 then
[0, 3, 0, 1, 1, 2, 1, 1, 2]
else
[0, 3, 0, 1, 1, 2, 2, 1, 0])))
else
(if i.val < 5452 then
(if i.val < 5450 then
(if i.val < 5449 then
[0, 3, 0, 1, 1, 2, 2, 1, 1]
else
[0, 3, 0, 1, 1, 2, 2, 3, 0])
else
(if i.val < 5451 then
[0, 3, 0, 1, 1, 2, 2, 3, 3]
else
[0, 3, 0, 1, 1, 2, 3, 0, 1]))
else
(if i.val < 5454 then
(if i.val < 5453 then
[0, 3, 0, 1, 1, 2, 3, 3, 0]
else
[0, 3, 0, 1, 2, 1, 0, 0, 3])
else
(if i.val < 5455 then
[0, 3, 0, 1, 2, 1, 0, 3, 0]
else
[0, 3, 0, 1, 2, 1, 0, 3, 2]))))
else
(if i.val < 5464 then
(if i.val < 5460 then
(if i.val < 5458 then
(if i.val < 5457 then
[0, 3, 0, 1, 2, 1, 1, 0, 0]
else
[0, 3, 0, 1, 2, 1, 1, 0, 3])
else
(if i.val < 5459 then
[0, 3, 0, 1, 2, 1, 1, 2, 3]
else
[0, 3, 0, 1, 2, 1, 1, 3, 2]))
else
(if i.val < 5462 then
(if i.val < 5461 then
[0, 3, 0, 1, 2, 1, 3, 2, 2]
else
[0, 3, 0, 1, 2, 2, 1, 3, 3])
else
(if i.val < 5463 then
[0, 3, 0, 1, 2, 2, 3, 0, 0]
else
[0, 3, 0, 1, 2, 2, 3, 3, 0])))
else
(if i.val < 5468 then
(if i.val < 5466 then
(if i.val < 5465 then
[0, 3, 0, 1, 2, 3, 0, 0, 3]
else
[0, 3, 0, 1, 2, 3, 0, 1, 1])
else
(if i.val < 5467 then
[0, 3, 0, 1, 2, 3, 0, 1, 2]
else
[0, 3, 0, 1, 2, 3, 3, 0, 1]))
else
(if i.val < 5470 then
(if i.val < 5469 then
[0, 3, 0, 1, 2, 3, 3, 0, 2]
else
[0, 3, 0, 1, 2, 3, 3, 2, 1])
else
(if i.val < 5471 then
[0, 3, 0, 2, 1, 0, 3, 0, 0]
else
[0, 3, 0, 2, 1, 0, 3, 2, 2])))))
else
(if i.val < 5488 then
(if i.val < 5480 then
(if i.val < 5476 then
(if i.val < 5474 then
(if i.val < 5473 then
[0, 3, 0, 2, 1, 1, 0, 0, 2]
else
[0, 3, 0, 2, 1, 1, 0, 2, 1])
else
(if i.val < 5475 then
[0, 3, 0, 2, 1, 1, 0, 2, 3]
else
[0, 3, 0, 2, 1, 1, 0, 3, 2]))
else
(if i.val < 5478 then
(if i.val < 5477 then
[0, 3, 0, 2, 1, 1, 2, 3, 0]
else
[0, 3, 0, 2, 1, 1, 2, 3, 2])
else
(if i.val < 5479 then
[0, 3, 0, 2, 1, 1, 3, 2, 2]
else
[0, 3, 0, 2, 1, 1, 3, 3, 2])))
else
(if i.val < 5484 then
(if i.val < 5482 then
(if i.val < 5481 then
[0, 3, 0, 2, 1, 3, 2, 2, 1]
else
[0, 3, 0, 2, 1, 3, 2, 2, 3])
else
(if i.val < 5483 then
[0, 3, 0, 2, 1, 3, 3, 0, 1]
else
[0, 3, 0, 2, 1, 3, 3, 0, 2]))
else
(if i.val < 5486 then
(if i.val < 5485 then
[0, 3, 0, 2, 1, 3, 3, 2, 1]
else
[0, 3, 0, 2, 1, 3, 3, 2, 2])
else
(if i.val < 5487 then
[0, 3, 0, 2, 2, 1, 0, 0, 3]
else
[0, 3, 0, 2, 2, 1, 0, 3, 0]))))
else
(if i.val < 5496 then
(if i.val < 5492 then
(if i.val < 5490 then
(if i.val < 5489 then
[0, 3, 0, 2, 2, 1, 0, 3, 3]
else
[0, 3, 0, 2, 2, 1, 1, 3, 0])
else
(if i.val < 5491 then
[0, 3, 0, 2, 2, 1, 1, 3, 3]
else
[0, 3, 0, 2, 2, 1, 3, 0, 0]))
else
(if i.val < 5494 then
(if i.val < 5493 then
[0, 3, 0, 2, 2, 1, 3, 0, 1]
else
[0, 3, 0, 2, 2, 1, 3, 0, 2])
else
(if i.val < 5495 then
[0, 3, 0, 2, 2, 1, 3, 3, 2]
else
[0, 3, 0, 2, 2, 3, 0, 1, 1])))
else
(if i.val < 5500 then
(if i.val < 5498 then
(if i.val < 5497 then
[0, 3, 0, 2, 2, 3, 0, 1, 2]
else
[0, 3, 0, 2, 3, 3, 0, 2, 1])
else
(if i.val < 5499 then
[0, 3, 0, 2, 3, 3, 2, 1, 0]
else
[0, 3, 2, 1, 0, 0, 1, 2, 2]))
else
(if i.val < 5502 then
(if i.val < 5501 then
[0, 3, 2, 1, 0, 0, 3, 2, 1]
else
[0, 3, 2, 1, 0, 0, 3, 3, 2])
else
(if i.val < 5503 then
[0, 3, 2, 1, 0, 3, 2, 1, 0]
else
[0, 3, 2, 1, 0, 3, 2, 1, 1])))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row31_cosetWordsPart0043 : Fin 8640 → List (Fin 4) :=
  fun i => (if i.val < 5568 then
(if i.val < 5536 then
(if i.val < 5520 then
(if i.val < 5512 then
(if i.val < 5508 then
(if i.val < 5506 then
(if i.val < 5505 then
[0, 3, 2, 1, 0, 3, 2, 2, 1]
else
[0, 3, 2, 1, 0, 3, 2, 2, 3])
else
(if i.val < 5507 then
[0, 3, 2, 1, 0, 3, 3, 0, 1]
else
[0, 3, 2, 1, 1, 0, 0, 2, 3]))
else
(if i.val < 5510 then
(if i.val < 5509 then
[0, 3, 2, 1, 1, 0, 0, 3, 2]
else
[0, 3, 2, 1, 1, 0, 2, 3, 2])
else
(if i.val < 5511 then
[0, 3, 2, 1, 1, 0, 2, 3, 3]
else
[0, 3, 2, 1, 1, 0, 3, 2, 1])))
else
(if i.val < 5516 then
(if i.val < 5514 then
(if i.val < 5513 then
[0, 3, 2, 1, 1, 0, 3, 3, 2]
else
[0, 3, 2, 1, 1, 2, 3, 0, 1])
else
(if i.val < 5515 then
[0, 3, 2, 2, 1, 0, 0, 1, 3]
else
[0, 3, 2, 2, 1, 0, 3, 0, 1]))
else
(if i.val < 5518 then
(if i.val < 5517 then
[0, 3, 2, 2, 1, 0, 3, 2, 1]
else
[0, 3, 2, 2, 1, 1, 0, 3, 2])
else
(if i.val < 5519 then
[0, 3, 2, 2, 1, 1, 0, 3, 3]
else
[0, 3, 2, 2, 1, 1, 3, 0, 0]))))
else
(if i.val < 5528 then
(if i.val < 5524 then
(if i.val < 5522 then
(if i.val < 5521 then
[0, 3, 2, 2, 1, 1, 3, 0, 1]
else
[0, 3, 2, 2, 1, 3, 0, 1, 1])
else
(if i.val < 5523 then
[0, 3, 2, 2, 1, 3, 0, 1, 2]
else
[0, 3, 2, 2, 1, 3, 0, 2, 1]))
else
(if i.val < 5526 then
(if i.val < 5525 then
[0, 3, 2, 2, 1, 3, 0, 2, 3]
else
[0, 3, 2, 2, 1, 3, 2, 2, 1])
else
(if i.val < 5527 then
[0, 3, 2, 2, 1, 3, 2, 2, 3]
else
[0, 3, 2, 2, 3, 0, 0, 3, 2])))
else
(if i.val < 5532 then
(if i.val < 5530 then
(if i.val < 5529 then
[0, 3, 2, 2, 3, 0, 1, 2, 3]
else
[0, 3, 3, 0, 0, 2, 1, 0, 0])
else
(if i.val < 5531 then
[0, 3, 3, 0, 0, 2, 1, 3, 2]
else
[0, 3, 3, 0, 0, 2, 1, 3, 3]))
else
(if i.val < 5534 then
(if i.val < 5533 then
[0, 3, 3, 0, 0, 2, 2, 1, 0]
else
[0, 3, 3, 0, 0, 2, 3, 3, 2])
else
(if i.val < 5535 then
[0, 3, 3, 0, 1, 1, 0, 2, 2]
else
[0, 3, 3, 0, 1, 1, 0, 2, 3])))))
else
(if i.val < 5552 then
(if i.val < 5544 then
(if i.val < 5540 then
(if i.val < 5538 then
(if i.val < 5537 then
[0, 3, 3, 0, 1, 1, 0, 3, 2]
else
[0, 3, 3, 0, 1, 1, 2, 2, 1])
else
(if i.val < 5539 then
[0, 3, 3, 0, 1, 1, 2, 2, 3]
else
[0, 3, 3, 0, 1, 1, 2, 3, 0]))
else
(if i.val < 5542 then
(if i.val < 5541 then
[0, 3, 3, 0, 1, 2, 1, 1, 0]
else
[0, 3, 3, 0, 1, 2, 1, 1, 3])
else
(if i.val < 5543 then
[0, 3, 3, 0, 1, 2, 1, 3, 3]
else
[0, 3, 3, 0, 1, 2, 2, 1, 1])))
else
(if i.val < 5548 then
(if i.val < 5546 then
(if i.val < 5545 then
[0, 3, 3, 0, 1, 2, 2, 1, 3]
else
[0, 3, 3, 0, 1, 2, 2, 3, 3])
else
(if i.val < 5547 then
[0, 3, 3, 0, 1, 2, 3, 0, 0]
else
[0, 3, 3, 0, 1, 2, 3, 0, 1]))
else
(if i.val < 5550 then
(if i.val < 5549 then
[0, 3, 3, 0, 1, 2, 3, 3, 2]
else
[0, 3, 3, 0, 2, 1, 0, 3, 0])
else
(if i.val < 5551 then
[0, 3, 3, 0, 2, 1, 0, 3, 3]
else
[0, 3, 3, 0, 2, 1, 1, 0, 3]))))
else
(if i.val < 5560 then
(if i.val < 5556 then
(if i.val < 5554 then
(if i.val < 5553 then
[0, 3, 3, 0, 2, 1, 1, 2, 3]
else
[0, 3, 3, 0, 2, 1, 1, 3, 2])
else
(if i.val < 5555 then
[0, 3, 3, 0, 2, 2, 1, 1, 3]
else
[0, 3, 3, 0, 2, 2, 1, 3, 0]))
else
(if i.val < 5558 then
(if i.val < 5557 then
[0, 3, 3, 0, 2, 3, 3, 0, 2]
else
[0, 3, 3, 0, 2, 3, 3, 2, 1])
else
(if i.val < 5559 then
[0, 3, 3, 2, 1, 0, 3, 2, 2]
else
[0, 3, 3, 2, 1, 0, 3, 3, 2])))
else
(if i.val < 5564 then
(if i.val < 5562 then
(if i.val < 5561 then
[0, 3, 3, 2, 1, 1, 0, 3, 2]
else
[0, 3, 3, 2, 1, 1, 0, 3, 3])
else
(if i.val < 5563 then
[0, 3, 3, 2, 1, 1, 2, 3, 3]
else
[0, 3, 3, 2, 2, 1, 0, 0, 3]))
else
(if i.val < 5566 then
(if i.val < 5565 then
[0, 3, 3, 2, 2, 1, 0, 3, 3]
else
[0, 3, 3, 2, 2, 1, 1, 0, 0])
else
(if i.val < 5567 then
[1, 0, 0, 1, 2, 1, 0, 0, 3]
else
[1, 0, 0, 1, 2, 1, 0, 3, 0]))))))
else
(if i.val < 5600 then
(if i.val < 5584 then
(if i.val < 5576 then
(if i.val < 5572 then
(if i.val < 5570 then
(if i.val < 5569 then
[1, 0, 0, 1, 2, 1, 0, 3, 2]
else
[1, 0, 0, 1, 2, 1, 0, 3, 3])
else
(if i.val < 5571 then
[1, 0, 0, 1, 2, 1, 1, 0, 3]
else
[1, 0, 0, 1, 2, 1, 1, 2, 3]))
else
(if i.val < 5574 then
(if i.val < 5573 then
[1, 0, 0, 1, 2, 1, 3, 0, 0]
else
[1, 0, 0, 1, 2, 1, 3, 0, 1])
else
(if i.val < 5575 then
[1, 0, 0, 1, 2, 1, 3, 3, 0]
else
[1, 0, 0, 1, 2, 1, 3, 3, 2])))
else
(if i.val < 5580 then
(if i.val < 5578 then
(if i.val < 5577 then
[1, 0, 0, 1, 2, 2, 1, 0, 0]
else
[1, 0, 0, 1, 2, 2, 1, 1, 0])
else
(if i.val < 5579 then
[1, 0, 0, 1, 2, 2, 1, 3, 0]
else
[1, 0, 0, 1, 2, 2, 1, 3, 2]))
else
(if i.val < 5582 then
(if i.val < 5581 then
[1, 0, 0, 1, 2, 2, 3, 0, 1]
else
[1, 0, 0, 1, 2, 2, 3, 2, 1])
else
(if i.val < 5583 then
[1, 0, 0, 1, 2, 3, 0, 0, 2]
else
[1, 0, 0, 1, 2, 3, 0, 0, 3]))))
else
(if i.val < 5592 then
(if i.val < 5588 then
(if i.val < 5586 then
(if i.val < 5585 then
[1, 0, 0, 1, 2, 3, 0, 1, 1]
else
[1, 0, 0, 1, 2, 3, 0, 2, 2])
else
(if i.val < 5587 then
[1, 0, 0, 1, 2, 3, 3, 0, 0]
else
[1, 0, 0, 1, 2, 3, 3, 0, 2]))
else
(if i.val < 5590 then
(if i.val < 5589 then
[1, 0, 0, 1, 2, 3, 3, 2, 2]
else
[1, 0, 0, 1, 3, 0, 0, 2, 2])
else
(if i.val < 5591 then
[1, 0, 0, 1, 3, 0, 1, 2, 1]
else
[1, 0, 0, 1, 3, 0, 1, 2, 2])))
else
(if i.val < 5596 then
(if i.val < 5594 then
(if i.val < 5593 then
[1, 0, 0, 1, 3, 0, 2, 1, 1]
else
[1, 0, 0, 1, 3, 2, 1, 1, 2])
else
(if i.val < 5595 then
[1, 0, 0, 1, 3, 3, 0, 0, 2]
else
[1, 0, 0, 1, 3, 3, 0, 1, 2]))
else
(if i.val < 5598 then
(if i.val < 5597 then
[1, 0, 0, 1, 3, 3, 0, 2, 2]
else
[1, 0, 0, 1, 3, 3, 0, 2, 3])
else
(if i.val < 5599 then
[1, 0, 0, 2, 1, 0, 0, 3, 2]
else
[1, 0, 0, 2, 1, 0, 3, 0, 2])))))
else
(if i.val < 5616 then
(if i.val < 5608 then
(if i.val < 5604 then
(if i.val < 5602 then
(if i.val < 5601 then
[1, 0, 0, 2, 1, 0, 3, 2, 1]
else
[1, 0, 0, 2, 1, 0, 3, 2, 2])
else
(if i.val < 5603 then
[1, 0, 0, 2, 1, 1, 0, 0, 2]
else
[1, 0, 0, 2, 1, 1, 0, 2, 1]))
else
(if i.val < 5606 then
(if i.val < 5605 then
[1, 0, 0, 2, 1, 1, 0, 3, 2]
else
[1, 0, 0, 2, 1, 1, 2, 3, 0])
else
(if i.val < 5607 then
[1, 0, 0, 2, 1, 1, 2, 3, 2]
else
[1, 0, 0, 2, 1, 1, 2, 3, 3])))
else
(if i.val < 5612 then
(if i.val < 5610 then
(if i.val < 5609 then
[1, 0, 0, 2, 1, 1, 3, 0, 2]
else
[1, 0, 0, 2, 1, 1, 3, 2, 1])
else
(if i.val < 5611 then
[1, 0, 0, 2, 1, 1, 3, 2, 2]
else
[1, 0, 0, 2, 1, 1, 3, 3, 2]))
else
(if i.val < 5614 then
(if i.val < 5613 then
[1, 0, 0, 2, 1, 3, 0, 1, 1]
else
[1, 0, 0, 2, 1, 3, 0, 2, 2])
else
(if i.val < 5615 then
[1, 0, 0, 2, 1, 3, 2, 2, 3]
else
[1, 0, 0, 2, 1, 3, 3, 0, 2]))))
else
(if i.val < 5624 then
(if i.val < 5620 then
(if i.val < 5618 then
(if i.val < 5617 then
[1, 0, 0, 2, 1, 3, 3, 2, 2]
else
[1, 0, 0, 2, 2, 1, 0, 3, 0])
else
(if i.val < 5619 then
[1, 0, 0, 2, 2, 1, 0, 3, 2]
else
[1, 0, 0, 2, 2, 1, 1, 0, 3]))
else
(if i.val < 5622 then
(if i.val < 5621 then
[1, 0, 0, 2, 2, 1, 1, 3, 2]
else
[1, 0, 0, 2, 2, 1, 1, 3, 3])
else
(if i.val < 5623 then
[1, 0, 0, 2, 2, 1, 3, 0, 0]
else
[1, 0, 0, 2, 2, 1, 3, 0, 1])))
else
(if i.val < 5628 then
(if i.val < 5626 then
(if i.val < 5625 then
[1, 0, 0, 2, 2, 1, 3, 3, 2]
else
[1, 0, 0, 2, 2, 3, 0, 0, 3])
else
(if i.val < 5627 then
[1, 0, 0, 2, 2, 3, 2, 2, 1]
else
[1, 0, 0, 2, 2, 3, 2, 2, 3]))
else
(if i.val < 5630 then
(if i.val < 5629 then
[1, 0, 0, 2, 2, 3, 3, 2, 1]
else
[1, 0, 0, 2, 2, 3, 3, 2, 2])
else
(if i.val < 5631 then
[1, 0, 0, 2, 3, 0, 0, 2, 2]
else
[1, 0, 0, 2, 3, 0, 0, 2, 3])))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row31_cosetWordsPart0044 : Fin 8640 → List (Fin 4) :=
  fun i => (if i.val < 5696 then
(if i.val < 5664 then
(if i.val < 5648 then
(if i.val < 5640 then
(if i.val < 5636 then
(if i.val < 5634 then
(if i.val < 5633 then
[1, 0, 0, 2, 3, 0, 1, 2, 2]
else
[1, 0, 0, 2, 3, 0, 2, 2, 1])
else
(if i.val < 5635 then
[1, 0, 0, 2, 3, 2, 1, 0, 3]
else
[1, 0, 0, 2, 3, 2, 1, 1, 0]))
else
(if i.val < 5638 then
(if i.val < 5637 then
[1, 0, 0, 2, 3, 2, 1, 1, 2]
else
[1, 0, 0, 2, 3, 2, 2, 1, 3])
else
(if i.val < 5639 then
[1, 0, 0, 2, 3, 2, 2, 3, 0]
else
[1, 0, 0, 2, 3, 3, 0, 1, 2])))
else
(if i.val < 5644 then
(if i.val < 5642 then
(if i.val < 5641 then
[1, 0, 0, 2, 3, 3, 0, 2, 1]
else
[1, 0, 0, 2, 3, 3, 0, 2, 2])
else
(if i.val < 5643 then
[1, 0, 0, 2, 3, 3, 2, 1, 0]
else
[1, 0, 0, 2, 3, 3, 2, 2, 1]))
else
(if i.val < 5646 then
(if i.val < 5645 then
[1, 0, 0, 3, 0, 0, 1, 1, 2]
else
[1, 0, 0, 3, 0, 0, 2, 2, 1])
else
(if i.val < 5647 then
[1, 0, 0, 3, 0, 0, 3, 2, 1]
else
[1, 0, 0, 3, 0, 0, 3, 2, 2]))))
else
(if i.val < 5656 then
(if i.val < 5652 then
(if i.val < 5650 then
(if i.val < 5649 then
[1, 0, 0, 3, 0, 1, 2, 1, 1]
else
[1, 0, 0, 3, 0, 1, 2, 2, 1])
else
(if i.val < 5651 then
[1, 0, 0, 3, 0, 1, 2, 2, 3]
else
[1, 0, 0, 3, 0, 1, 2, 3, 3]))
else
(if i.val < 5654 then
(if i.val < 5653 then
[1, 0, 0, 3, 0, 2, 1, 1, 0]
else
[1, 0, 0, 3, 0, 2, 1, 1, 2])
else
(if i.val < 5655 then
[1, 0, 0, 3, 0, 2, 2, 1, 0]
else
[1, 0, 0, 3, 0, 2, 2, 3, 0])))
else
(if i.val < 5660 then
(if i.val < 5658 then
(if i.val < 5657 then
[1, 0, 0, 3, 0, 2, 2, 3, 3]
else
[1, 0, 0, 3, 2, 1, 1, 2, 3])
else
(if i.val < 5659 then
[1, 0, 0, 3, 2, 2, 1, 1, 3]
else
[1, 0, 0, 3, 2, 2, 3, 0, 0]))
else
(if i.val < 5662 then
(if i.val < 5661 then
[1, 0, 0, 3, 2, 2, 3, 0, 1]
else
[1, 0, 0, 3, 3, 0, 0, 2, 1])
else
(if i.val < 5663 then
[1, 0, 0, 3, 3, 0, 0, 2, 2]
else
[1, 0, 0, 3, 3, 0, 0, 2, 3])))))
else
(if i.val < 5680 then
(if i.val < 5672 then
(if i.val < 5668 then
(if i.val < 5666 then
(if i.val < 5665 then
[1, 0, 0, 3, 3, 0, 1, 2, 3]
else
[1, 0, 0, 3, 3, 0, 2, 1, 0])
else
(if i.val < 5667 then
[1, 0, 0, 3, 3, 0, 2, 1, 1]
else
[1, 0, 0, 3, 3, 0, 2, 1, 3]))
else
(if i.val < 5670 then
(if i.val < 5669 then
[1, 0, 0, 3, 3, 0, 2, 3, 3]
else
[1, 0, 0, 3, 3, 2, 1, 0, 0])
else
(if i.val < 5671 then
[1, 0, 0, 3, 3, 2, 1, 0, 3]
else
[1, 0, 0, 3, 3, 2, 1, 1, 0])))
else
(if i.val < 5676 then
(if i.val < 5674 then
(if i.val < 5673 then
[1, 0, 0, 3, 3, 2, 1, 1, 2]
else
[1, 0, 0, 3, 3, 2, 2, 1, 0])
else
(if i.val < 5675 then
[1, 0, 0, 3, 3, 2, 2, 1, 1]
else
[1, 0, 2, 1, 0, 0, 1, 3, 2]))
else
(if i.val < 5678 then
(if i.val < 5677 then
[1, 0, 2, 1, 0, 3, 2, 2, 1]
else
[1, 0, 2, 1, 0, 3, 2, 2, 3])
else
(if i.val < 5679 then
[1, 0, 2, 1, 0, 3, 3, 0, 1]
else
[1, 0, 2, 1, 0, 3, 3, 2, 1]))))
else
(if i.val < 5688 then
(if i.val < 5684 then
(if i.val < 5682 then
(if i.val < 5681 then
[1, 0, 2, 1, 0, 3, 3, 2, 2]
else
[1, 0, 2, 1, 1, 0, 0, 2, 1])
else
(if i.val < 5683 then
[1, 0, 2, 1, 1, 0, 0, 2, 3]
else
[1, 0, 2, 1, 1, 0, 2, 1, 1]))
else
(if i.val < 5686 then
(if i.val < 5685 then
[1, 0, 2, 1, 1, 0, 2, 1, 3]
else
[1, 0, 2, 1, 1, 0, 2, 3, 0])
else
(if i.val < 5687 then
[1, 0, 2, 1, 1, 0, 2, 3, 2]
else
[1, 0, 2, 1, 1, 0, 2, 3, 3])))
else
(if i.val < 5692 then
(if i.val < 5690 then
(if i.val < 5689 then
[1, 0, 2, 1, 1, 0, 3, 2, 1]
else
[1, 0, 2, 1, 1, 0, 3, 3, 2])
else
(if i.val < 5691 then
[1, 0, 2, 1, 1, 2, 3, 0, 0]
else
[1, 0, 2, 1, 1, 2, 3, 0, 1]))
else
(if i.val < 5694 then
(if i.val < 5693 then
[1, 0, 2, 1, 1, 2, 3, 0, 2]
else
[1, 0, 2, 1, 1, 2, 3, 3, 0])
else
(if i.val < 5695 then
[1, 0, 2, 1, 1, 2, 3, 3, 2]
else
[1, 0, 2, 1, 1, 3, 0, 2, 1]))))))
else
(if i.val < 5728 then
(if i.val < 5712 then
(if i.val < 5704 then
(if i.val < 5700 then
(if i.val < 5698 then
(if i.val < 5697 then
[1, 0, 2, 1, 1, 3, 0, 2, 2]
else
[1, 0, 2, 1, 1, 3, 0, 2, 3])
else
(if i.val < 5699 then
[1, 0, 2, 1, 1, 3, 2, 1, 0]
else
[1, 0, 2, 1, 1, 3, 2, 1, 1]))
else
(if i.val < 5702 then
(if i.val < 5701 then
[1, 0, 2, 1, 1, 3, 2, 2, 3]
else
[1, 0, 2, 1, 3, 0, 0, 1, 2])
else
(if i.val < 5703 then
[1, 0, 2, 1, 3, 2, 2, 3, 0]
else
[1, 0, 2, 1, 3, 3, 0, 1, 2])))
else
(if i.val < 5708 then
(if i.val < 5706 then
(if i.val < 5705 then
[1, 0, 2, 1, 3, 3, 2, 2, 1]
else
[1, 0, 2, 2, 1, 0, 0, 1, 3])
else
(if i.val < 5707 then
[1, 0, 2, 2, 1, 0, 3, 0, 0]
else
[1, 0, 2, 2, 1, 0, 3, 0, 1]))
else
(if i.val < 5710 then
(if i.val < 5709 then
[1, 0, 2, 2, 1, 0, 3, 2, 1]
else
[1, 0, 2, 2, 1, 0, 3, 2, 2])
else
(if i.val < 5711 then
[1, 0, 2, 2, 1, 0, 3, 3, 2]
else
[1, 0, 2, 2, 1, 1, 0, 3, 2]))))
else
(if i.val < 5720 then
(if i.val < 5716 then
(if i.val < 5714 then
(if i.val < 5713 then
[1, 0, 2, 2, 1, 1, 3, 0, 1]
else
[1, 0, 2, 2, 1, 1, 3, 2, 1])
else
(if i.val < 5715 then
[1, 0, 2, 2, 1, 3, 0, 0, 2]
else
[1, 0, 2, 2, 1, 3, 0, 1, 2]))
else
(if i.val < 5718 then
(if i.val < 5717 then
[1, 0, 2, 2, 1, 3, 2, 1, 0]
else
[1, 0, 2, 2, 1, 3, 2, 1, 1])
else
(if i.val < 5719 then
[1, 0, 2, 2, 1, 3, 3, 0, 2]
else
[1, 0, 2, 2, 1, 3, 3, 2, 2])))
else
(if i.val < 5724 then
(if i.val < 5722 then
(if i.val < 5721 then
[1, 0, 2, 2, 3, 0, 0, 2, 2]
else
[1, 0, 2, 2, 3, 0, 0, 3, 2])
else
(if i.val < 5723 then
[1, 0, 2, 2, 3, 0, 1, 1, 2]
else
[1, 0, 2, 2, 3, 0, 1, 2, 3]))
else
(if i.val < 5726 then
(if i.val < 5725 then
[1, 0, 2, 2, 3, 0, 2, 1, 0]
else
[1, 0, 2, 2, 3, 0, 2, 2, 1])
else
(if i.val < 5727 then
[1, 0, 2, 2, 3, 0, 2, 2, 3]
else
[1, 0, 2, 2, 3, 0, 2, 3, 3])))))
else
(if i.val < 5744 then
(if i.val < 5736 then
(if i.val < 5732 then
(if i.val < 5730 then
(if i.val < 5729 then
[1, 0, 2, 2, 3, 2, 1, 0, 3]
else
[1, 0, 2, 2, 3, 2, 2, 1, 0])
else
(if i.val < 5731 then
[1, 0, 2, 2, 3, 2, 2, 1, 3]
else
[1, 0, 2, 2, 3, 2, 2, 3, 0]))
else
(if i.val < 5734 then
(if i.val < 5733 then
[1, 0, 2, 2, 3, 3, 0, 0, 2]
else
[1, 0, 2, 2, 3, 3, 0, 1, 2])
else
(if i.val < 5735 then
[1, 0, 2, 2, 3, 3, 0, 2, 2]
else
[1, 0, 2, 2, 3, 3, 0, 2, 3])))
else
(if i.val < 5740 then
(if i.val < 5738 then
(if i.val < 5737 then
[1, 0, 2, 2, 3, 3, 2, 1, 0]
else
[1, 0, 2, 3, 0, 0, 2, 1, 0])
else
(if i.val < 5739 then
[1, 0, 2, 3, 0, 0, 3, 2, 1]
else
[1, 0, 2, 3, 0, 1, 1, 0, 2]))
else
(if i.val < 5742 then
(if i.val < 5741 then
[1, 0, 2, 3, 0, 1, 1, 2, 1]
else
[1, 0, 2, 3, 0, 1, 1, 2, 2])
else
(if i.val < 5743 then
[1, 0, 2, 3, 0, 1, 1, 2, 3]
else
[1, 0, 2, 3, 0, 1, 2, 2, 1]))))
else
(if i.val < 5752 then
(if i.val < 5748 then
(if i.val < 5746 then
(if i.val < 5745 then
[1, 0, 2, 3, 0, 1, 2, 2, 3]
else
[1, 0, 2, 3, 0, 2, 1, 0, 0])
else
(if i.val < 5747 then
[1, 0, 2, 3, 0, 2, 1, 0, 3]
else
[1, 0, 2, 3, 0, 2, 1, 1, 2]))
else
(if i.val < 5750 then
(if i.val < 5749 then
[1, 0, 2, 3, 0, 2, 1, 1, 3]
else
[1, 0, 2, 3, 0, 2, 1, 3, 2])
else
(if i.val < 5751 then
[1, 0, 2, 3, 0, 2, 1, 3, 3]
else
[1, 0, 2, 3, 0, 2, 3, 3, 2])))
else
(if i.val < 5756 then
(if i.val < 5754 then
(if i.val < 5753 then
[1, 0, 2, 3, 2, 1, 0, 3, 2]
else
[1, 0, 2, 3, 2, 1, 0, 3, 3])
else
(if i.val < 5755 then
[1, 0, 2, 3, 2, 1, 1, 0, 0]
else
[1, 0, 2, 3, 2, 1, 1, 0, 3]))
else
(if i.val < 5758 then
(if i.val < 5757 then
[1, 0, 2, 3, 2, 1, 1, 2, 3]
else
[1, 0, 2, 3, 2, 2, 3, 0, 1])
else
(if i.val < 5759 then
[1, 0, 2, 3, 3, 0, 0, 2, 1]
else
[1, 0, 2, 3, 3, 0, 0, 2, 3])))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row31_cosetWordsPart0045 : Fin 8640 → List (Fin 4) :=
  fun i => (if i.val < 5824 then
(if i.val < 5792 then
(if i.val < 5776 then
(if i.val < 5768 then
(if i.val < 5764 then
(if i.val < 5762 then
(if i.val < 5761 then
[1, 0, 2, 3, 3, 0, 1, 1, 2]
else
[1, 0, 2, 3, 3, 0, 1, 2, 1])
else
(if i.val < 5763 then
[1, 0, 2, 3, 3, 0, 1, 2, 3]
else
[1, 0, 2, 3, 3, 0, 2, 1, 1]))
else
(if i.val < 5766 then
(if i.val < 5765 then
[1, 0, 2, 3, 3, 0, 2, 1, 3]
else
[1, 0, 2, 3, 3, 0, 2, 2, 1])
else
(if i.val < 5767 then
[1, 0, 2, 3, 3, 0, 2, 3, 3]
else
[1, 0, 2, 3, 3, 2, 1, 0, 0])))
else
(if i.val < 5772 then
(if i.val < 5770 then
(if i.val < 5769 then
[1, 0, 2, 3, 3, 2, 1, 0, 3]
else
[1, 0, 3, 0, 0, 1, 1, 2, 1])
else
(if i.val < 5771 then
[1, 0, 3, 0, 0, 1, 1, 2, 2]
else
[1, 0, 3, 0, 0, 1, 1, 2, 3]))
else
(if i.val < 5774 then
(if i.val < 5773 then
[1, 0, 3, 0, 0, 1, 2, 1, 1]
else
[1, 0, 3, 0, 0, 1, 2, 2, 1])
else
(if i.val < 5775 then
[1, 0, 3, 0, 0, 1, 2, 3, 2]
else
[1, 0, 3, 0, 0, 1, 2, 3, 3]))))
else
(if i.val < 5784 then
(if i.val < 5780 then
(if i.val < 5778 then
(if i.val < 5777 then
[1, 0, 3, 0, 0, 1, 3, 2, 2]
else
[1, 0, 3, 0, 0, 2, 1, 0, 0])
else
(if i.val < 5779 then
[1, 0, 3, 0, 0, 2, 1, 1, 2]
else
[1, 0, 3, 0, 0, 2, 1, 3, 3]))
else
(if i.val < 5782 then
(if i.val < 5781 then
[1, 0, 3, 0, 0, 2, 2, 1, 3]
else
[1, 0, 3, 0, 0, 2, 2, 3, 2])
else
(if i.val < 5783 then
[1, 0, 3, 0, 0, 2, 3, 3, 2]
else
[1, 0, 3, 0, 0, 3, 2, 1, 0])))
else
(if i.val < 5788 then
(if i.val < 5786 then
(if i.val < 5785 then
[1, 0, 3, 0, 0, 3, 2, 2, 1]
else
[1, 0, 3, 0, 1, 1, 0, 2, 1])
else
(if i.val < 5787 then
[1, 0, 3, 0, 1, 1, 0, 2, 2]
else
[1, 0, 3, 0, 1, 1, 2, 1, 1]))
else
(if i.val < 5790 then
(if i.val < 5789 then
[1, 0, 3, 0, 1, 1, 2, 2, 1]
else
[1, 0, 3, 0, 1, 1, 2, 2, 3])
else
(if i.val < 5791 then
[1, 0, 3, 0, 1, 1, 2, 3, 3]
else
[1, 0, 3, 0, 1, 2, 1, 1, 2])))))
else
(if i.val < 5808 then
(if i.val < 5800 then
(if i.val < 5796 then
(if i.val < 5794 then
(if i.val < 5793 then
[1, 0, 3, 0, 1, 2, 1, 3, 2]
else
[1, 0, 3, 0, 1, 2, 1, 3, 3])
else
(if i.val < 5795 then
[1, 0, 3, 0, 1, 2, 3, 0, 1]
else
[1, 0, 3, 0, 1, 2, 3, 3, 2]))
else
(if i.val < 5798 then
(if i.val < 5797 then
[1, 0, 3, 0, 2, 1, 0, 3, 3]
else
[1, 0, 3, 0, 2, 1, 1, 0, 2])
else
(if i.val < 5799 then
[1, 0, 3, 0, 2, 1, 1, 0, 3]
else
[1, 0, 3, 0, 2, 1, 3, 3, 0])))
else
(if i.val < 5804 then
(if i.val < 5802 then
(if i.val < 5801 then
[1, 0, 3, 0, 2, 2, 1, 0, 3]
else
[1, 0, 3, 0, 2, 2, 1, 1, 3])
else
(if i.val < 5803 then
[1, 0, 3, 0, 2, 2, 1, 3, 2]
else
[1, 0, 3, 0, 2, 2, 3, 0, 1]))
else
(if i.val < 5806 then
(if i.val < 5805 then
[1, 0, 3, 0, 2, 3, 3, 0, 1]
else
[1, 0, 3, 0, 2, 3, 3, 0, 2])
else
(if i.val < 5807 then
[1, 0, 3, 0, 2, 3, 3, 2, 1]
else
[1, 0, 3, 2, 1, 0, 0, 1, 2]))))
else
(if i.val < 5816 then
(if i.val < 5812 then
(if i.val < 5810 then
(if i.val < 5809 then
[1, 0, 3, 2, 1, 0, 0, 1, 3]
else
[1, 0, 3, 2, 1, 0, 0, 3, 2])
else
(if i.val < 5811 then
[1, 0, 3, 2, 1, 1, 0, 0, 2]
else
[1, 0, 3, 2, 1, 1, 0, 2, 1]))
else
(if i.val < 5814 then
(if i.val < 5813 then
[1, 0, 3, 2, 1, 1, 0, 2, 3]
else
[1, 0, 3, 2, 1, 1, 0, 3, 2])
else
(if i.val < 5815 then
[1, 0, 3, 2, 1, 1, 2, 3, 0]
else
[1, 0, 3, 2, 2, 1, 0, 0, 3])))
else
(if i.val < 5820 then
(if i.val < 5818 then
(if i.val < 5817 then
[1, 0, 3, 2, 2, 1, 0, 3, 2]
else
[1, 0, 3, 2, 2, 1, 1, 3, 0])
else
(if i.val < 5819 then
[1, 0, 3, 2, 2, 1, 3, 0, 0]
else
[1, 0, 3, 2, 2, 1, 3, 0, 1]))
else
(if i.val < 5822 then
(if i.val < 5821 then
[1, 0, 3, 2, 2, 3, 0, 0, 3]
else
[1, 0, 3, 2, 2, 3, 0, 1, 2])
else
(if i.val < 5823 then
[1, 0, 3, 3, 0, 0, 2, 2, 1]
else
[1, 0, 3, 3, 0, 0, 2, 3, 3]))))))
else
(if i.val < 5856 then
(if i.val < 5840 then
(if i.val < 5832 then
(if i.val < 5828 then
(if i.val < 5826 then
(if i.val < 5825 then
[1, 0, 3, 3, 0, 1, 1, 0, 2]
else
[1, 0, 3, 3, 0, 1, 2, 1, 0])
else
(if i.val < 5827 then
[1, 0, 3, 3, 0, 1, 2, 1, 1]
else
[1, 0, 3, 3, 0, 1, 2, 1, 3]))
else
(if i.val < 5830 then
(if i.val < 5829 then
[1, 0, 3, 3, 0, 1, 2, 2, 1]
else
[1, 0, 3, 3, 0, 1, 2, 2, 3])
else
(if i.val < 5831 then
[1, 0, 3, 3, 0, 1, 2, 3, 3]
else
[1, 0, 3, 3, 0, 2, 1, 0, 0])))
else
(if i.val < 5836 then
(if i.val < 5834 then
(if i.val < 5833 then
[1, 0, 3, 3, 0, 2, 2, 1, 0]
else
[1, 0, 3, 3, 0, 2, 2, 3, 3])
else
(if i.val < 5835 then
[1, 0, 3, 3, 0, 2, 3, 3, 2]
else
[1, 0, 3, 3, 2, 1, 0, 3, 2]))
else
(if i.val < 5838 then
(if i.val < 5837 then
[1, 0, 3, 3, 2, 2, 1, 0, 3]
else
[1, 1, 0, 0, 2, 1, 0, 3, 0])
else
(if i.val < 5839 then
[1, 1, 0, 0, 2, 1, 0, 3, 2]
else
[1, 1, 0, 0, 2, 1, 1, 2, 3]))))
else
(if i.val < 5848 then
(if i.val < 5844 then
(if i.val < 5842 then
(if i.val < 5841 then
[1, 1, 0, 0, 2, 1, 3, 0, 0]
else
[1, 1, 0, 0, 2, 1, 3, 0, 1])
else
(if i.val < 5843 then
[1, 1, 0, 0, 2, 2, 1, 0, 0]
else
[1, 1, 0, 0, 2, 2, 1, 1, 3]))
else
(if i.val < 5846 then
(if i.val < 5845 then
[1, 1, 0, 0, 2, 2, 1, 3, 0]
else
[1, 1, 0, 0, 2, 2, 1, 3, 3])
else
(if i.val < 5847 then
[1, 1, 0, 0, 2, 2, 3, 0, 0]
else
[1, 1, 0, 0, 2, 2, 3, 0, 1])))
else
(if i.val < 5852 then
(if i.val < 5850 then
(if i.val < 5849 then
[1, 1, 0, 0, 2, 2, 3, 2, 1]
else
[1, 1, 0, 0, 2, 3, 0, 0, 2])
else
(if i.val < 5851 then
[1, 1, 0, 0, 2, 3, 0, 0, 3]
else
[1, 1, 0, 0, 2, 3, 0, 1, 1]))
else
(if i.val < 5854 then
(if i.val < 5853 then
[1, 1, 0, 0, 2, 3, 0, 2, 2]
else
[1, 1, 0, 0, 2, 3, 3, 0, 2])
else
(if i.val < 5855 then
[1, 1, 0, 0, 2, 3, 3, 2, 1]
else
[1, 1, 0, 0, 3, 0, 0, 2, 2])))))
else
(if i.val < 5872 then
(if i.val < 5864 then
(if i.val < 5860 then
(if i.val < 5858 then
(if i.val < 5857 then
[1, 1, 0, 0, 3, 0, 0, 3, 2]
else
[1, 1, 0, 0, 3, 0, 1, 2, 1])
else
(if i.val < 5859 then
[1, 1, 0, 0, 3, 0, 1, 2, 2]
else
[1, 1, 0, 0, 3, 0, 1, 2, 3]))
else
(if i.val < 5862 then
(if i.val < 5861 then
[1, 1, 0, 0, 3, 0, 2, 1, 1]
else
[1, 1, 0, 0, 3, 2, 2, 1, 3])
else
(if i.val < 5863 then
[1, 1, 0, 0, 3, 3, 0, 2, 1]
else
[1, 1, 0, 0, 3, 3, 0, 2, 2])))
else
(if i.val < 5868 then
(if i.val < 5866 then
(if i.val < 5865 then
[1, 1, 0, 0, 3, 3, 0, 2, 3]
else
[1, 1, 0, 2, 1, 0, 0, 1, 2])
else
(if i.val < 5867 then
[1, 1, 0, 2, 1, 0, 0, 1, 3]
else
[1, 1, 0, 2, 1, 0, 3, 0, 0]))
else
(if i.val < 5870 then
(if i.val < 5869 then
[1, 1, 0, 2, 1, 0, 3, 0, 1]
else
[1, 1, 0, 2, 1, 0, 3, 2, 1])
else
(if i.val < 5871 then
[1, 1, 0, 2, 1, 0, 3, 2, 2]
else
[1, 1, 0, 2, 1, 0, 3, 3, 2]))))
else
(if i.val < 5880 then
(if i.val < 5876 then
(if i.val < 5874 then
(if i.val < 5873 then
[1, 1, 0, 2, 1, 1, 0, 2, 1]
else
[1, 1, 0, 2, 1, 1, 0, 2, 3])
else
(if i.val < 5875 then
[1, 1, 0, 2, 1, 1, 0, 3, 2]
else
[1, 1, 0, 2, 1, 1, 2, 3, 0]))
else
(if i.val < 5878 then
(if i.val < 5877 then
[1, 1, 0, 2, 1, 1, 2, 3, 2]
else
[1, 1, 0, 2, 1, 1, 2, 3, 3])
else
(if i.val < 5879 then
[1, 1, 0, 2, 1, 1, 3, 0, 1]
else
[1, 1, 0, 2, 1, 1, 3, 0, 2])))
else
(if i.val < 5884 then
(if i.val < 5882 then
(if i.val < 5881 then
[1, 1, 0, 2, 1, 1, 3, 2, 1]
else
[1, 1, 0, 2, 1, 1, 3, 2, 2])
else
(if i.val < 5883 then
[1, 1, 0, 2, 1, 3, 2, 2, 1]
else
[1, 1, 0, 2, 1, 3, 2, 2, 3]))
else
(if i.val < 5886 then
(if i.val < 5885 then
[1, 1, 0, 2, 1, 3, 3, 0, 1]
else
[1, 1, 0, 2, 1, 3, 3, 2, 2])
else
(if i.val < 5887 then
[1, 1, 0, 2, 2, 1, 0, 0, 3]
else
[1, 1, 0, 2, 2, 1, 0, 3, 0])))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row31_cosetWordsPart0046 : Fin 8640 → List (Fin 4) :=
  fun i => (if i.val < 5952 then
(if i.val < 5920 then
(if i.val < 5904 then
(if i.val < 5896 then
(if i.val < 5892 then
(if i.val < 5890 then
(if i.val < 5889 then
[1, 1, 0, 2, 2, 1, 0, 3, 3]
else
[1, 1, 0, 2, 2, 1, 1, 0, 3])
else
(if i.val < 5891 then
[1, 1, 0, 2, 2, 1, 1, 3, 2]
else
[1, 1, 0, 2, 2, 1, 3, 0, 0]))
else
(if i.val < 5894 then
(if i.val < 5893 then
[1, 1, 0, 2, 2, 1, 3, 0, 1]
else
[1, 1, 0, 2, 2, 1, 3, 3, 0])
else
(if i.val < 5895 then
[1, 1, 0, 2, 2, 1, 3, 3, 2]
else
[1, 1, 0, 2, 2, 3, 0, 0, 2])))
else
(if i.val < 5900 then
(if i.val < 5898 then
(if i.val < 5897 then
[1, 1, 0, 2, 2, 3, 0, 1, 1]
else
[1, 1, 0, 2, 2, 3, 0, 1, 2])
else
(if i.val < 5899 then
[1, 1, 0, 2, 2, 3, 0, 2, 2]
else
[1, 1, 0, 2, 2, 3, 0, 2, 3]))
else
(if i.val < 5902 then
(if i.val < 5901 then
[1, 1, 0, 2, 2, 3, 2, 1, 0]
else
[1, 1, 0, 2, 2, 3, 2, 1, 1])
else
(if i.val < 5903 then
[1, 1, 0, 2, 2, 3, 2, 2, 1]
else
[1, 1, 0, 2, 2, 3, 2, 2, 3]))))
else
(if i.val < 5912 then
(if i.val < 5908 then
(if i.val < 5906 then
(if i.val < 5905 then
[1, 1, 0, 2, 3, 0, 0, 2, 3]
else
[1, 1, 0, 2, 3, 0, 1, 1, 2])
else
(if i.val < 5907 then
[1, 1, 0, 2, 3, 0, 1, 2, 2]
else
[1, 1, 0, 2, 3, 0, 2, 1, 0]))
else
(if i.val < 5910 then
(if i.val < 5909 then
[1, 1, 0, 2, 3, 0, 2, 1, 1]
else
[1, 1, 0, 2, 3, 0, 2, 1, 3])
else
(if i.val < 5911 then
[1, 1, 0, 2, 3, 2, 1, 0, 0]
else
[1, 1, 0, 2, 3, 2, 1, 0, 3])))
else
(if i.val < 5916 then
(if i.val < 5914 then
(if i.val < 5913 then
[1, 1, 0, 2, 3, 3, 0, 1, 2]
else
[1, 1, 0, 2, 3, 3, 0, 2, 1])
else
(if i.val < 5915 then
[1, 1, 0, 2, 3, 3, 0, 2, 2]
else
[1, 1, 0, 2, 3, 3, 0, 2, 3]))
else
(if i.val < 5918 then
(if i.val < 5917 then
[1, 1, 0, 2, 3, 3, 2, 1, 0]
else
[1, 1, 0, 2, 3, 3, 2, 1, 1])
else
(if i.val < 5919 then
[1, 1, 0, 3, 0, 0, 1, 1, 2]
else
[1, 1, 0, 3, 0, 0, 1, 3, 2])))))
else
(if i.val < 5936 then
(if i.val < 5928 then
(if i.val < 5924 then
(if i.val < 5922 then
(if i.val < 5921 then
[1, 1, 0, 3, 0, 0, 2, 1, 0]
else
[1, 1, 0, 3, 0, 0, 2, 1, 1])
else
(if i.val < 5923 then
[1, 1, 0, 3, 0, 0, 2, 1, 3]
else
[1, 1, 0, 3, 0, 0, 2, 2, 1]))
else
(if i.val < 5926 then
(if i.val < 5925 then
[1, 1, 0, 3, 0, 0, 2, 3, 2]
else
[1, 1, 0, 3, 0, 0, 2, 3, 3])
else
(if i.val < 5927 then
[1, 1, 0, 3, 0, 0, 3, 2, 1]
else
[1, 1, 0, 3, 0, 1, 1, 2, 2])))
else
(if i.val < 5932 then
(if i.val < 5930 then
(if i.val < 5929 then
[1, 1, 0, 3, 0, 1, 1, 2, 3]
else
[1, 1, 0, 3, 0, 1, 2, 1, 1])
else
(if i.val < 5931 then
[1, 1, 0, 3, 0, 1, 2, 2, 1]
else
[1, 1, 0, 3, 0, 1, 2, 3, 3]))
else
(if i.val < 5934 then
(if i.val < 5933 then
[1, 1, 0, 3, 0, 2, 1, 0, 0]
else
[1, 1, 0, 3, 0, 2, 1, 0, 3])
else
(if i.val < 5935 then
[1, 1, 0, 3, 0, 2, 1, 1, 0]
else
[1, 1, 0, 3, 0, 2, 2, 1, 3]))))
else
(if i.val < 5944 then
(if i.val < 5940 then
(if i.val < 5938 then
(if i.val < 5937 then
[1, 1, 0, 3, 0, 2, 2, 3, 0]
else
[1, 1, 0, 3, 0, 2, 3, 3, 2])
else
(if i.val < 5939 then
[1, 1, 0, 3, 2, 1, 0, 0, 3]
else
[1, 1, 0, 3, 2, 1, 1, 0, 0]))
else
(if i.val < 5942 then
(if i.val < 5941 then
[1, 1, 0, 3, 2, 1, 1, 2, 3]
else
[1, 1, 0, 3, 2, 2, 1, 0, 0])
else
(if i.val < 5943 then
[1, 1, 0, 3, 2, 2, 1, 1, 3]
else
[1, 1, 0, 3, 2, 2, 1, 3, 0])))
else
(if i.val < 5948 then
(if i.val < 5946 then
(if i.val < 5945 then
[1, 1, 0, 3, 2, 2, 1, 3, 2]
else
[1, 1, 0, 3, 2, 2, 3, 0, 0])
else
(if i.val < 5947 then
[1, 1, 0, 3, 2, 2, 3, 0, 1]
else
[1, 1, 0, 3, 3, 0, 1, 2, 1]))
else
(if i.val < 5950 then
(if i.val < 5949 then
[1, 1, 0, 3, 3, 0, 1, 2, 2]
else
[1, 1, 0, 3, 3, 0, 2, 2, 1])
else
(if i.val < 5951 then
[1, 1, 0, 3, 3, 2, 2, 1, 1]
else
[1, 1, 2, 1, 0, 0, 1, 3, 2]))))))
else
(if i.val < 5984 then
(if i.val < 5968 then
(if i.val < 5960 then
(if i.val < 5956 then
(if i.val < 5954 then
(if i.val < 5953 then
[1, 1, 2, 1, 0, 3, 0, 2, 1]
else
[1, 1, 2, 1, 0, 3, 0, 2, 2])
else
(if i.val < 5955 then
[1, 1, 2, 1, 0, 3, 2, 1, 1]
else
[1, 1, 2, 1, 0, 3, 2, 2, 3]))
else
(if i.val < 5958 then
(if i.val < 5957 then
[1, 1, 2, 1, 0, 3, 3, 0, 1]
else
[1, 1, 2, 1, 0, 3, 3, 2, 2])
else
(if i.val < 5959 then
[1, 1, 2, 1, 1, 0, 2, 1, 3]
else
[1, 1, 2, 1, 1, 0, 2, 3, 0])))
else
(if i.val < 5964 then
(if i.val < 5962 then
(if i.val < 5961 then
[1, 1, 2, 1, 1, 0, 2, 3, 2]
else
[1, 1, 2, 1, 1, 0, 3, 0, 2])
else
(if i.val < 5963 then
[1, 1, 2, 1, 1, 0, 3, 2, 1]
else
[1, 1, 2, 1, 1, 0, 3, 3, 2]))
else
(if i.val < 5966 then
(if i.val < 5965 then
[1, 1, 2, 1, 1, 2, 3, 0, 1]
else
[1, 1, 2, 1, 1, 2, 3, 2, 1])
else
(if i.val < 5967 then
[1, 1, 2, 1, 1, 3, 2, 1, 1]
else
[1, 1, 2, 1, 1, 3, 2, 2, 1]))))
else
(if i.val < 5976 then
(if i.val < 5972 then
(if i.val < 5970 then
(if i.val < 5969 then
[1, 1, 2, 1, 3, 0, 0, 1, 2]
else
[1, 1, 2, 1, 3, 0, 0, 3, 2])
else
(if i.val < 5971 then
[1, 1, 2, 1, 3, 0, 1, 2, 2]
else
[1, 1, 2, 1, 3, 0, 1, 2, 3]))
else
(if i.val < 5974 then
(if i.val < 5973 then
[1, 1, 2, 1, 3, 2, 2, 1, 3]
else
[1, 1, 2, 1, 3, 3, 0, 1, 2])
else
(if i.val < 5975 then
[1, 1, 2, 1, 3, 3, 0, 2, 2]
else
[1, 1, 2, 1, 3, 3, 2, 2, 1])))
else
(if i.val < 5980 then
(if i.val < 5978 then
(if i.val < 5977 then
[1, 1, 2, 2, 1, 0, 0, 1, 3]
else
[1, 1, 2, 2, 1, 0, 3, 0, 1])
else
(if i.val < 5979 then
[1, 1, 2, 2, 1, 0, 3, 2, 1]
else
[1, 1, 2, 2, 1, 0, 3, 3, 2]))
else
(if i.val < 5982 then
(if i.val < 5981 then
[1, 1, 2, 2, 1, 1, 0, 3, 2]
else
[1, 1, 2, 2, 1, 1, 0, 3, 3])
else
(if i.val < 5983 then
[1, 1, 2, 2, 1, 1, 3, 0, 0]
else
[1, 1, 2, 2, 1, 1, 3, 0, 1])))))
else
(if i.val < 6000 then
(if i.val < 5992 then
(if i.val < 5988 then
(if i.val < 5986 then
(if i.val < 5985 then
[1, 1, 2, 2, 1, 1, 3, 0, 2]
else
[1, 1, 2, 2, 1, 3, 0, 0, 2])
else
(if i.val < 5987 then
[1, 1, 2, 2, 1, 3, 0, 1, 2]
else
[1, 1, 2, 2, 1, 3, 2, 1, 1]))
else
(if i.val < 5990 then
(if i.val < 5989 then
[1, 1, 2, 2, 1, 3, 3, 0, 1]
else
[1, 1, 2, 2, 1, 3, 3, 2, 1])
else
(if i.val < 5991 then
[1, 1, 2, 2, 3, 0, 0, 3, 2]
else
[1, 1, 2, 2, 3, 0, 1, 2, 3])))
else
(if i.val < 5996 then
(if i.val < 5994 then
(if i.val < 5993 then
[1, 1, 2, 2, 3, 2, 2, 1, 3]
else
[1, 1, 2, 2, 3, 3, 0, 1, 2])
else
(if i.val < 5995 then
[1, 1, 2, 3, 0, 0, 1, 1, 2]
else
[1, 1, 2, 3, 0, 0, 2, 1, 1]))
else
(if i.val < 5998 then
(if i.val < 5997 then
[1, 1, 2, 3, 0, 1, 1, 2, 1]
else
[1, 1, 2, 3, 0, 1, 1, 2, 2])
else
(if i.val < 5999 then
[1, 1, 2, 3, 0, 1, 1, 2, 3]
else
[1, 1, 2, 3, 0, 1, 2, 2, 1]))))
else
(if i.val < 6008 then
(if i.val < 6004 then
(if i.val < 6002 then
(if i.val < 6001 then
[1, 1, 2, 3, 0, 1, 2, 2, 3]
else
[1, 1, 2, 3, 0, 1, 2, 3, 0])
else
(if i.val < 6003 then
[1, 1, 2, 3, 0, 2, 1, 0, 0]
else
[1, 1, 2, 3, 0, 2, 1, 0, 3]))
else
(if i.val < 6006 then
(if i.val < 6005 then
[1, 1, 2, 3, 0, 2, 1, 3, 3]
else
[1, 1, 2, 3, 0, 2, 2, 1, 3])
else
(if i.val < 6007 then
[1, 1, 2, 3, 0, 2, 2, 3, 0]
else
[1, 1, 2, 3, 2, 1, 1, 0, 0])))
else
(if i.val < 6012 then
(if i.val < 6010 then
(if i.val < 6009 then
[1, 1, 2, 3, 2, 2, 1, 1, 3]
else
[1, 1, 2, 3, 2, 2, 1, 3, 0])
else
(if i.val < 6011 then
[1, 1, 2, 3, 2, 2, 3, 0, 0]
else
[1, 1, 2, 3, 3, 0, 0, 2, 3]))
else
(if i.val < 6014 then
(if i.val < 6013 then
[1, 1, 2, 3, 3, 0, 1, 1, 2]
else
[1, 1, 2, 3, 3, 0, 1, 2, 1])
else
(if i.val < 6015 then
[1, 1, 2, 3, 3, 0, 1, 2, 2]
else
[1, 1, 2, 3, 3, 0, 2, 2, 1])))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row31_cosetWordsPart0047 : Fin 8640 → List (Fin 4) :=
  fun i => (if i.val < 6080 then
(if i.val < 6048 then
(if i.val < 6032 then
(if i.val < 6024 then
(if i.val < 6020 then
(if i.val < 6018 then
(if i.val < 6017 then
[1, 1, 2, 3, 3, 0, 2, 2, 3]
else
[1, 1, 2, 3, 3, 2, 1, 0, 3])
else
(if i.val < 6019 then
[1, 1, 3, 0, 0, 1, 1, 2, 2]
else
[1, 1, 3, 0, 0, 1, 1, 2, 3]))
else
(if i.val < 6022 then
(if i.val < 6021 then
[1, 1, 3, 0, 0, 1, 2, 3, 3]
else
[1, 1, 3, 0, 0, 2, 1, 1, 2])
else
(if i.val < 6023 then
[1, 1, 3, 0, 0, 2, 2, 3, 3]
else
[1, 1, 3, 0, 0, 2, 3, 2, 1])))
else
(if i.val < 6028 then
(if i.val < 6026 then
(if i.val < 6025 then
[1, 1, 3, 0, 0, 2, 3, 3, 2]
else
[1, 1, 3, 0, 0, 3, 2, 2, 1])
else
(if i.val < 6027 then
[1, 1, 3, 0, 1, 1, 0, 2, 1]
else
[1, 1, 3, 0, 1, 1, 2, 1, 0]))
else
(if i.val < 6030 then
(if i.val < 6029 then
[1, 1, 3, 0, 1, 1, 2, 2, 1]
else
[1, 1, 3, 0, 1, 1, 2, 2, 3])
else
(if i.val < 6031 then
[1, 1, 3, 0, 1, 1, 2, 3, 3]
else
[1, 1, 3, 0, 1, 2, 1, 3, 0]))))
else
(if i.val < 6040 then
(if i.val < 6036 then
(if i.val < 6034 then
(if i.val < 6033 then
[1, 1, 3, 0, 1, 2, 1, 3, 3]
else
[1, 1, 3, 0, 1, 2, 2, 1, 0])
else
(if i.val < 6035 then
[1, 1, 3, 0, 1, 2, 2, 1, 3]
else
[1, 1, 3, 0, 1, 2, 3, 0, 1]))
else
(if i.val < 6038 then
(if i.val < 6037 then
[1, 1, 3, 0, 1, 2, 3, 3, 2]
else
[1, 1, 3, 0, 2, 1, 0, 3, 3])
else
(if i.val < 6039 then
[1, 1, 3, 0, 2, 1, 1, 3, 2]
else
[1, 1, 3, 0, 2, 2, 1, 0, 0])))
else
(if i.val < 6044 then
(if i.val < 6042 then
(if i.val < 6041 then
[1, 1, 3, 0, 2, 2, 1, 0, 3]
else
[1, 1, 3, 0, 2, 3, 3, 0, 2])
else
(if i.val < 6043 then
[1, 1, 3, 0, 2, 3, 3, 2, 1]
else
[1, 1, 3, 2, 1, 0, 3, 2, 1]))
else
(if i.val < 6046 then
(if i.val < 6045 then
[1, 1, 3, 2, 1, 0, 3, 2, 2]
else
[1, 1, 3, 2, 1, 0, 3, 3, 2])
else
(if i.val < 6047 then
[1, 1, 3, 2, 1, 1, 2, 3, 3]
else
[1, 1, 3, 2, 2, 1, 0, 0, 3])))))
else
(if i.val < 6064 then
(if i.val < 6056 then
(if i.val < 6052 then
(if i.val < 6050 then
(if i.val < 6049 then
[1, 1, 3, 2, 2, 1, 0, 3, 2]
else
[1, 1, 3, 2, 2, 1, 3, 0, 1])
else
(if i.val < 6051 then
[1, 1, 3, 2, 2, 3, 0, 1, 1]
else
[1, 1, 3, 2, 2, 3, 0, 1, 2]))
else
(if i.val < 6054 then
(if i.val < 6053 then
[1, 1, 3, 3, 0, 0, 2, 1, 3]
else
[1, 1, 3, 3, 0, 0, 2, 2, 3])
else
(if i.val < 6055 then
[1, 1, 3, 3, 0, 0, 2, 3, 3]
else
[1, 1, 3, 3, 0, 1, 1, 0, 2])))
else
(if i.val < 6060 then
(if i.val < 6058 then
(if i.val < 6057 then
[1, 1, 3, 3, 0, 1, 2, 1, 0]
else
[1, 1, 3, 3, 0, 1, 2, 1, 1])
else
(if i.val < 6059 then
[1, 1, 3, 3, 0, 1, 2, 1, 3]
else
[1, 1, 3, 3, 0, 1, 2, 2, 1]))
else
(if i.val < 6062 then
(if i.val < 6061 then
[1, 1, 3, 3, 0, 1, 2, 2, 3]
else
[1, 1, 3, 3, 0, 2, 1, 0, 0])
else
(if i.val < 6063 then
[1, 1, 3, 3, 0, 2, 1, 3, 2]
else
[1, 1, 3, 3, 0, 2, 2, 1, 0]))))
else
(if i.val < 6072 then
(if i.val < 6068 then
(if i.val < 6066 then
(if i.val < 6065 then
[1, 1, 3, 3, 0, 2, 2, 1, 1]
else
[1, 1, 3, 3, 0, 2, 3, 3, 2])
else
(if i.val < 6067 then
[1, 2, 1, 0, 0, 1, 2, 3, 0]
else
[1, 2, 1, 0, 0, 1, 3, 0, 2]))
else
(if i.val < 6070 then
(if i.val < 6069 then
[1, 2, 1, 0, 0, 3, 0, 1, 2]
else
[1, 2, 1, 0, 0, 3, 2, 2, 1])
else
(if i.val < 6071 then
[1, 2, 1, 0, 0, 3, 3, 2, 2]
else
[1, 2, 1, 0, 3, 0, 1, 1, 2])))
else
(if i.val < 6076 then
(if i.val < 6074 then
(if i.val < 6073 then
[1, 2, 1, 0, 3, 0, 1, 2, 1]
else
[1, 2, 1, 0, 3, 0, 1, 2, 3])
else
(if i.val < 6075 then
[1, 2, 1, 0, 3, 0, 2, 1, 1]
else
[1, 2, 1, 0, 3, 0, 2, 1, 3]))
else
(if i.val < 6078 then
(if i.val < 6077 then
[1, 2, 1, 0, 3, 0, 2, 2, 1]
else
[1, 2, 1, 0, 3, 2, 1, 1, 0])
else
(if i.val < 6079 then
[1, 2, 1, 0, 3, 3, 0, 2, 1]
else
[1, 2, 1, 0, 3, 3, 0, 2, 2]))))))
else
(if i.val < 6112 then
(if i.val < 6096 then
(if i.val < 6088 then
(if i.val < 6084 then
(if i.val < 6082 then
(if i.val < 6081 then
[1, 2, 1, 0, 3, 3, 2, 1, 0]
else
[1, 2, 1, 0, 3, 3, 2, 1, 1])
else
(if i.val < 6083 then
[1, 2, 1, 1, 0, 0, 2, 1, 3]
else
[1, 2, 1, 1, 0, 0, 3, 2, 2]))
else
(if i.val < 6086 then
(if i.val < 6085 then
[1, 2, 1, 1, 0, 2, 1, 3, 0]
else
[1, 2, 1, 1, 0, 2, 1, 3, 2])
else
(if i.val < 6087 then
[1, 2, 1, 1, 0, 2, 3, 0, 0]
else
[1, 2, 1, 1, 0, 2, 3, 0, 1])))
else
(if i.val < 6092 then
(if i.val < 6090 then
(if i.val < 6089 then
[1, 2, 1, 1, 0, 2, 3, 0, 2]
else
[1, 2, 1, 1, 0, 2, 3, 2, 1])
else
(if i.val < 6091 then
[1, 2, 1, 1, 0, 3, 0, 2, 1]
else
[1, 2, 1, 1, 0, 3, 0, 2, 3]))
else
(if i.val < 6094 then
(if i.val < 6093 then
[1, 2, 1, 1, 0, 3, 2, 1, 0]
else
[1, 2, 1, 1, 2, 3, 0, 0, 2])
else
(if i.val < 6095 then
[1, 2, 1, 1, 2, 3, 2, 1, 0]
else
[1, 2, 1, 1, 2, 3, 2, 1, 1]))))
else
(if i.val < 6104 then
(if i.val < 6100 then
(if i.val < 6098 then
(if i.val < 6097 then
[1, 2, 1, 1, 2, 3, 2, 2, 1]
else
[1, 2, 1, 1, 2, 3, 3, 0, 0])
else
(if i.val < 6099 then
[1, 2, 1, 1, 2, 3, 3, 0, 1]
else
[1, 2, 1, 1, 3, 0, 1, 1, 2]))
else
(if i.val < 6102 then
(if i.val < 6101 then
[1, 2, 1, 1, 3, 0, 1, 2, 1]
else
[1, 2, 1, 1, 3, 0, 1, 2, 2])
else
(if i.val < 6103 then
[1, 2, 1, 1, 3, 0, 1, 2, 3]
else
[1, 2, 1, 1, 3, 0, 2, 1, 0])))
else
(if i.val < 6108 then
(if i.val < 6106 then
(if i.val < 6105 then
[1, 2, 1, 1, 3, 0, 2, 2, 3]
else
[1, 2, 1, 1, 3, 2, 2, 1, 1])
else
(if i.val < 6107 then
[1, 2, 1, 1, 3, 2, 2, 1, 3]
else
[1, 2, 1, 1, 3, 2, 2, 3, 0]))
else
(if i.val < 6110 then
(if i.val < 6109 then
[1, 2, 1, 3, 0, 0, 1, 2, 3]
else
[1, 2, 1, 3, 0, 0, 2, 2, 3])
else
(if i.val < 6111 then
[1, 2, 1, 3, 0, 0, 3, 2, 1]
else
[1, 2, 1, 3, 0, 0, 3, 2, 2])))))
else
(if i.val < 6128 then
(if i.val < 6120 then
(if i.val < 6116 then
(if i.val < 6114 then
(if i.val < 6113 then
[1, 2, 1, 3, 0, 1, 2, 1, 0]
else
[1, 2, 1, 3, 0, 1, 2, 1, 3])
else
(if i.val < 6115 then
[1, 2, 1, 3, 0, 1, 2, 2, 1]
else
[1, 2, 1, 3, 0, 1, 2, 2, 3]))
else
(if i.val < 6118 then
(if i.val < 6117 then
[1, 2, 1, 3, 0, 1, 2, 3, 0]
else
[1, 2, 1, 3, 0, 1, 2, 3, 3])
else
(if i.val < 6119 then
[1, 2, 1, 3, 0, 2, 1, 1, 2]
else
[1, 2, 1, 3, 0, 2, 3, 3, 2])))
else
(if i.val < 6124 then
(if i.val < 6122 then
(if i.val < 6121 then
[1, 2, 1, 3, 2, 1, 0, 3, 2]
else
[1, 2, 1, 3, 2, 1, 1, 2, 3])
else
(if i.val < 6123 then
[1, 2, 1, 3, 2, 2, 1, 0, 0]
else
[1, 2, 1, 3, 2, 2, 1, 1, 3]))
else
(if i.val < 6126 then
(if i.val < 6125 then
[1, 2, 1, 3, 3, 0, 0, 1, 2]
else
[1, 2, 1, 3, 3, 0, 0, 2, 2])
else
(if i.val < 6127 then
[1, 2, 1, 3, 3, 0, 1, 2, 1]
else
[1, 2, 1, 3, 3, 0, 1, 2, 2]))))
else
(if i.val < 6136 then
(if i.val < 6132 then
(if i.val < 6130 then
(if i.val < 6129 then
[1, 2, 1, 3, 3, 0, 1, 2, 3]
else
[1, 2, 1, 3, 3, 0, 2, 2, 1])
else
(if i.val < 6131 then
[1, 2, 1, 3, 3, 0, 2, 2, 3]
else
[1, 2, 1, 3, 3, 2, 2, 1, 1]))
else
(if i.val < 6134 then
(if i.val < 6133 then
[1, 2, 2, 1, 0, 0, 1, 2, 3]
else
[1, 2, 2, 1, 0, 0, 3, 2, 2])
else
(if i.val < 6135 then
[1, 2, 2, 1, 0, 3, 0, 2, 1]
else
[1, 2, 2, 1, 0, 3, 0, 2, 3])))
else
(if i.val < 6140 then
(if i.val < 6138 then
(if i.val < 6137 then
[1, 2, 2, 1, 0, 3, 2, 1, 0]
else
[1, 2, 2, 1, 0, 3, 2, 1, 1])
else
(if i.val < 6139 then
[1, 2, 2, 1, 0, 3, 2, 2, 3]
else
[1, 2, 2, 1, 0, 3, 3, 0, 1]))
else
(if i.val < 6142 then
(if i.val < 6141 then
[1, 2, 2, 1, 1, 0, 3, 0, 2]
else
[1, 2, 2, 1, 1, 0, 3, 2, 1])
else
(if i.val < 6143 then
[1, 2, 2, 1, 1, 0, 3, 3, 2]
else
[1, 2, 2, 1, 1, 3, 0, 2, 1])))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row31_cosetWordsPart0048 : Fin 8640 → List (Fin 4) :=
  fun i => (if i.val < 6208 then
(if i.val < 6176 then
(if i.val < 6160 then
(if i.val < 6152 then
(if i.val < 6148 then
(if i.val < 6146 then
(if i.val < 6145 then
[1, 2, 2, 1, 1, 3, 2, 1, 0]
else
[1, 2, 2, 1, 1, 3, 2, 1, 1])
else
(if i.val < 6147 then
[1, 2, 2, 1, 3, 0, 0, 1, 2]
else
[1, 2, 2, 1, 3, 0, 0, 2, 3]))
else
(if i.val < 6150 then
(if i.val < 6149 then
[1, 2, 2, 1, 3, 0, 0, 3, 2]
else
[1, 2, 2, 1, 3, 0, 1, 2, 1])
else
(if i.val < 6151 then
[1, 2, 2, 1, 3, 0, 2, 1, 0]
else
[1, 2, 2, 1, 3, 3, 0, 1, 2])))
else
(if i.val < 6156 then
(if i.val < 6154 then
(if i.val < 6153 then
[1, 2, 2, 1, 3, 3, 0, 2, 3]
else
[1, 2, 2, 1, 3, 3, 2, 1, 1])
else
(if i.val < 6155 then
[1, 2, 2, 3, 0, 0, 1, 1, 2]
else
[1, 2, 2, 3, 0, 0, 1, 2, 1]))
else
(if i.val < 6158 then
(if i.val < 6157 then
[1, 2, 2, 3, 0, 0, 1, 2, 2]
else
[1, 2, 2, 3, 0, 0, 1, 2, 3])
else
(if i.val < 6159 then
[1, 2, 2, 3, 0, 0, 3, 2, 1]
else
[1, 2, 2, 3, 0, 1, 2, 3, 0]))))
else
(if i.val < 6168 then
(if i.val < 6164 then
(if i.val < 6162 then
(if i.val < 6161 then
[1, 2, 2, 3, 0, 1, 2, 3, 3]
else
[1, 2, 2, 3, 0, 2, 2, 1, 3])
else
(if i.val < 6163 then
[1, 2, 2, 3, 0, 2, 2, 3, 3]
else
[1, 2, 2, 3, 0, 2, 3, 3, 2]))
else
(if i.val < 6166 then
(if i.val < 6165 then
[1, 2, 2, 3, 2, 2, 1, 1, 3]
else
[1, 2, 2, 3, 2, 2, 3, 0, 1])
else
(if i.val < 6167 then
[1, 2, 2, 3, 3, 0, 2, 2, 3]
else
[1, 2, 2, 3, 3, 2, 2, 1, 1])))
else
(if i.val < 6172 then
(if i.val < 6170 then
(if i.val < 6169 then
[1, 2, 3, 0, 0, 1, 1, 2, 1]
else
[1, 2, 3, 0, 0, 1, 1, 2, 3])
else
(if i.val < 6171 then
[1, 2, 3, 0, 0, 1, 3, 2, 2]
else
[1, 2, 3, 0, 0, 2, 1, 1, 2]))
else
(if i.val < 6174 then
(if i.val < 6173 then
[1, 2, 3, 0, 0, 2, 2, 1, 1]
else
[1, 2, 3, 0, 0, 2, 3, 3, 2])
else
(if i.val < 6175 then
[1, 2, 3, 0, 0, 3, 2, 2, 1]
else
[1, 2, 3, 0, 1, 1, 0, 2, 1])))))
else
(if i.val < 6192 then
(if i.val < 6184 then
(if i.val < 6180 then
(if i.val < 6178 then
(if i.val < 6177 then
[1, 2, 3, 0, 1, 1, 2, 1, 0]
else
[1, 2, 3, 0, 1, 1, 2, 1, 1])
else
(if i.val < 6179 then
[1, 2, 3, 0, 1, 1, 2, 3, 3]
else
[1, 2, 3, 0, 1, 2, 1, 1, 0]))
else
(if i.val < 6182 then
(if i.val < 6181 then
[1, 2, 3, 0, 1, 2, 1, 3, 0]
else
[1, 2, 3, 0, 1, 2, 1, 3, 2])
else
(if i.val < 6183 then
[1, 2, 3, 0, 1, 2, 1, 3, 3]
else
[1, 2, 3, 0, 1, 2, 2, 1, 0])))
else
(if i.val < 6188 then
(if i.val < 6186 then
(if i.val < 6185 then
[1, 2, 3, 0, 1, 2, 2, 1, 1]
else
[1, 2, 3, 0, 1, 2, 2, 1, 3])
else
(if i.val < 6187 then
[1, 2, 3, 0, 1, 2, 2, 3, 0]
else
[1, 2, 3, 0, 1, 2, 3, 3, 2]))
else
(if i.val < 6190 then
(if i.val < 6189 then
[1, 2, 3, 0, 2, 1, 1, 2, 3]
else
[1, 2, 3, 0, 2, 1, 3, 3, 2])
else
(if i.val < 6191 then
[1, 2, 3, 0, 2, 2, 1, 0, 0]
else
[1, 2, 3, 0, 2, 2, 1, 0, 3]))))
else
(if i.val < 6200 then
(if i.val < 6196 then
(if i.val < 6194 then
(if i.val < 6193 then
[1, 2, 3, 0, 2, 2, 1, 3, 3]
else
[1, 2, 3, 0, 2, 3, 3, 2, 1])
else
(if i.val < 6195 then
[1, 2, 3, 2, 1, 0, 3, 2, 2]
else
[1, 2, 3, 2, 2, 1, 3, 2, 2]))
else
(if i.val < 6198 then
(if i.val < 6197 then
[1, 2, 3, 3, 0, 0, 2, 1, 3]
else
[1, 2, 3, 3, 0, 0, 2, 2, 3])
else
(if i.val < 6199 then
[1, 2, 3, 3, 0, 1, 2, 1, 0]
else
[1, 2, 3, 3, 0, 1, 2, 1, 1])))
else
(if i.val < 6204 then
(if i.val < 6202 then
(if i.val < 6201 then
[1, 2, 3, 3, 0, 1, 2, 1, 3]
else
[1, 2, 3, 3, 0, 1, 2, 3, 0])
else
(if i.val < 6203 then
[1, 2, 3, 3, 0, 1, 2, 3, 3]
else
[1, 2, 3, 3, 0, 2, 1, 0, 3]))
else
(if i.val < 6206 then
(if i.val < 6205 then
[1, 2, 3, 3, 0, 2, 1, 1, 3]
else
[1, 2, 3, 3, 0, 2, 1, 3, 2])
else
(if i.val < 6207 then
[1, 2, 3, 3, 0, 2, 1, 3, 3]
else
[1, 2, 3, 3, 0, 2, 2, 1, 0]))))))
else
(if i.val < 6240 then
(if i.val < 6224 then
(if i.val < 6216 then
(if i.val < 6212 then
(if i.val < 6210 then
(if i.val < 6209 then
[1, 2, 3, 3, 0, 2, 2, 1, 1]
else
[1, 2, 3, 3, 0, 2, 2, 1, 3])
else
(if i.val < 6211 then
[1, 2, 3, 3, 0, 2, 3, 3, 2]
else
[1, 2, 3, 3, 2, 1, 0, 0, 3]))
else
(if i.val < 6214 then
(if i.val < 6213 then
[1, 3, 0, 0, 1, 1, 2, 1, 0]
else
[1, 3, 0, 0, 1, 1, 2, 1, 1])
else
(if i.val < 6215 then
[1, 3, 0, 0, 1, 1, 2, 1, 3]
else
[1, 3, 0, 0, 1, 1, 2, 2, 1])))
else
(if i.val < 6220 then
(if i.val < 6218 then
(if i.val < 6217 then
[1, 3, 0, 0, 1, 1, 2, 2, 3]
else
[1, 3, 0, 0, 1, 1, 2, 3, 0])
else
(if i.val < 6219 then
[1, 3, 0, 0, 1, 1, 2, 3, 2]
else
[1, 3, 0, 0, 1, 1, 2, 3, 3]))
else
(if i.val < 6222 then
(if i.val < 6221 then
[1, 3, 0, 0, 1, 2, 1, 1, 2]
else
[1, 3, 0, 0, 1, 2, 1, 1, 3])
else
(if i.val < 6223 then
[1, 3, 0, 0, 1, 2, 1, 3, 3]
else
[1, 3, 0, 0, 1, 2, 2, 1, 1]))))
else
(if i.val < 6232 then
(if i.val < 6228 then
(if i.val < 6226 then
(if i.val < 6225 then
[1, 3, 0, 0, 1, 2, 2, 1, 3]
else
[1, 3, 0, 0, 1, 2, 2, 3, 0])
else
(if i.val < 6227 then
[1, 3, 0, 0, 1, 2, 2, 3, 3]
else
[1, 3, 0, 0, 1, 2, 3, 0, 1]))
else
(if i.val < 6230 then
(if i.val < 6229 then
[1, 3, 0, 0, 1, 2, 3, 0, 2]
else
[1, 3, 0, 0, 1, 2, 3, 3, 2])
else
(if i.val < 6231 then
[1, 3, 0, 0, 1, 3, 0, 0, 2]
else
[1, 3, 0, 0, 2, 1, 0, 3, 2])))
else
(if i.val < 6236 then
(if i.val < 6234 then
(if i.val < 6233 then
[1, 3, 0, 0, 2, 1, 1, 0, 2]
else
[1, 3, 0, 0, 2, 1, 1, 2, 3])
else
(if i.val < 6235 then
[1, 3, 0, 0, 2, 1, 1, 3, 2]
else
[1, 3, 0, 0, 2, 2, 3, 0, 1]))
else
(if i.val < 6238 then
(if i.val < 6237 then
[1, 3, 0, 0, 2, 2, 3, 2, 2]
else
[1, 3, 0, 0, 2, 2, 3, 3, 2])
else
(if i.val < 6239 then
[1, 3, 0, 0, 2, 3, 2, 1, 1]
else
[1, 3, 0, 0, 2, 3, 3, 2, 1])))))
else
(if i.val < 6256 then
(if i.val < 6248 then
(if i.val < 6244 then
(if i.val < 6242 then
(if i.val < 6241 then
[1, 3, 0, 0, 3, 2, 1, 1, 0]
else
[1, 3, 0, 0, 3, 2, 1, 1, 2])
else
(if i.val < 6243 then
[1, 3, 0, 0, 3, 2, 2, 1, 1]
else
[1, 3, 0, 0, 3, 2, 2, 1, 3]))
else
(if i.val < 6246 then
(if i.val < 6245 then
[1, 3, 0, 0, 3, 2, 2, 3, 0]
else
[1, 3, 0, 1, 1, 0, 2, 2, 1])
else
(if i.val < 6247 then
[1, 3, 0, 1, 1, 0, 2, 3, 3]
else
[1, 3, 0, 1, 1, 2, 2, 1, 0])))
else
(if i.val < 6252 then
(if i.val < 6250 then
(if i.val < 6249 then
[1, 3, 0, 1, 1, 2, 2, 1, 1]
else
[1, 3, 0, 1, 1, 2, 2, 3, 0])
else
(if i.val < 6251 then
[1, 3, 0, 1, 1, 2, 2, 3, 3]
else
[1, 3, 0, 1, 1, 2, 3, 3, 0]))
else
(if i.val < 6254 then
(if i.val < 6253 then
[1, 3, 0, 1, 2, 1, 0, 0, 3]
else
[1, 3, 0, 1, 2, 1, 0, 3, 2])
else
(if i.val < 6255 then
[1, 3, 0, 1, 2, 1, 1, 0, 2]
else
[1, 3, 0, 1, 2, 1, 1, 0, 3]))))
else
(if i.val < 6264 then
(if i.val < 6260 then
(if i.val < 6258 then
(if i.val < 6257 then
[1, 3, 0, 1, 2, 1, 1, 2, 3]
else
[1, 3, 0, 1, 2, 1, 1, 3, 0])
else
(if i.val < 6259 then
[1, 3, 0, 1, 2, 1, 1, 3, 3]
else
[1, 3, 0, 1, 2, 1, 3, 3, 2]))
else
(if i.val < 6262 then
(if i.val < 6261 then
[1, 3, 0, 1, 2, 2, 1, 3, 2]
else
[1, 3, 0, 1, 2, 2, 3, 0, 0])
else
(if i.val < 6263 then
[1, 3, 0, 1, 2, 3, 0, 0, 3]
else
[1, 3, 0, 1, 2, 3, 0, 1, 1])))
else
(if i.val < 6268 then
(if i.val < 6266 then
(if i.val < 6265 then
[1, 3, 0, 1, 2, 3, 3, 0, 1]
else
[1, 3, 0, 2, 1, 0, 3, 2, 2])
else
(if i.val < 6267 then
[1, 3, 0, 2, 1, 0, 3, 3, 2]
else
[1, 3, 0, 2, 1, 1, 0, 2, 1]))
else
(if i.val < 6270 then
(if i.val < 6269 then
[1, 3, 0, 2, 1, 1, 0, 2, 3]
else
[1, 3, 0, 2, 1, 1, 2, 3, 2])
else
(if i.val < 6271 then
[1, 3, 0, 2, 1, 1, 2, 3, 3]
else
[1, 3, 0, 2, 1, 1, 3, 2, 2])))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row31_cosetWordsPart0049 : Fin 8640 → List (Fin 4) :=
  fun i => (if i.val < 6336 then
(if i.val < 6304 then
(if i.val < 6288 then
(if i.val < 6280 then
(if i.val < 6276 then
(if i.val < 6274 then
(if i.val < 6273 then
[1, 3, 0, 2, 1, 3, 3, 0, 2]
else
[1, 3, 0, 2, 1, 3, 3, 2, 1])
else
(if i.val < 6275 then
[1, 3, 0, 2, 1, 3, 3, 2, 2]
else
[1, 3, 0, 2, 2, 1, 3, 3, 2]))
else
(if i.val < 6278 then
(if i.val < 6277 then
[1, 3, 0, 2, 3, 3, 0, 2, 1]
else
[1, 3, 0, 2, 3, 3, 2, 1, 1])
else
(if i.val < 6279 then
[1, 3, 2, 1, 0, 0, 3, 2, 1]
else
[1, 3, 2, 1, 0, 0, 3, 3, 2])))
else
(if i.val < 6284 then
(if i.val < 6282 then
(if i.val < 6281 then
[1, 3, 2, 1, 0, 3, 2, 1, 0]
else
[1, 3, 2, 1, 1, 0, 0, 2, 3])
else
(if i.val < 6283 then
[1, 3, 2, 1, 1, 0, 0, 3, 2]
else
[1, 3, 2, 1, 1, 0, 2, 3, 0]))
else
(if i.val < 6286 then
(if i.val < 6285 then
[1, 3, 2, 1, 1, 2, 3, 3, 2]
else
[1, 3, 2, 2, 1, 0, 0, 3, 2])
else
(if i.val < 6287 then
[1, 3, 2, 2, 1, 0, 3, 2, 1]
else
[1, 3, 2, 2, 1, 1, 3, 0, 1]))))
else
(if i.val < 6296 then
(if i.val < 6292 then
(if i.val < 6290 then
(if i.val < 6289 then
[1, 3, 2, 2, 1, 3, 0, 1, 2]
else
[1, 3, 2, 2, 3, 0, 0, 1, 2])
else
(if i.val < 6291 then
[1, 3, 2, 2, 3, 0, 1, 2, 2]
else
[1, 3, 2, 2, 3, 0, 1, 2, 3]))
else
(if i.val < 6294 then
(if i.val < 6293 then
[1, 3, 3, 0, 0, 1, 1, 2, 1]
else
[1, 3, 3, 0, 0, 1, 1, 2, 2])
else
(if i.val < 6295 then
[1, 3, 3, 0, 0, 1, 1, 2, 3]
else
[1, 3, 3, 0, 0, 1, 2, 1, 3])))
else
(if i.val < 6300 then
(if i.val < 6298 then
(if i.val < 6297 then
[1, 3, 3, 0, 0, 1, 2, 2, 3]
else
[1, 3, 3, 0, 0, 1, 2, 3, 0])
else
(if i.val < 6299 then
[1, 3, 3, 0, 0, 2, 1, 1, 2]
else
[1, 3, 3, 0, 0, 2, 2, 1, 3]))
else
(if i.val < 6302 then
(if i.val < 6301 then
[1, 3, 3, 0, 0, 2, 3, 3, 2]
else
[1, 3, 3, 0, 1, 1, 0, 2, 2])
else
(if i.val < 6303 then
[1, 3, 3, 0, 1, 1, 2, 1, 1]
else
[1, 3, 3, 0, 1, 2, 1, 0, 0])))))
else
(if i.val < 6320 then
(if i.val < 6312 then
(if i.val < 6308 then
(if i.val < 6306 then
(if i.val < 6305 then
[1, 3, 3, 0, 1, 2, 1, 1, 0]
else
[1, 3, 3, 0, 1, 2, 1, 1, 2])
else
(if i.val < 6307 then
[1, 3, 3, 0, 1, 2, 2, 1, 0]
else
[1, 3, 3, 0, 1, 2, 2, 1, 1]))
else
(if i.val < 6310 then
(if i.val < 6309 then
[1, 3, 3, 0, 1, 2, 3, 0, 0]
else
[1, 3, 3, 0, 1, 2, 3, 0, 1])
else
(if i.val < 6311 then
[1, 3, 3, 0, 2, 1, 0, 3, 3]
else
[1, 3, 3, 0, 2, 1, 1, 2, 3])))
else
(if i.val < 6316 then
(if i.val < 6314 then
(if i.val < 6313 then
[1, 3, 3, 0, 2, 1, 1, 3, 2]
else
[1, 3, 3, 0, 2, 1, 3, 3, 2])
else
(if i.val < 6315 then
[1, 3, 3, 0, 2, 2, 1, 0, 3]
else
[1, 3, 3, 0, 2, 3, 3, 0, 2]))
else
(if i.val < 6318 then
(if i.val < 6317 then
[1, 3, 3, 2, 1, 0, 3, 2, 2]
else
[1, 3, 3, 2, 1, 0, 3, 3, 2])
else
(if i.val < 6319 then
[1, 3, 3, 2, 1, 1, 0, 2, 3]
else
[1, 3, 3, 2, 1, 1, 2, 3, 3]))))
else
(if i.val < 6328 then
(if i.val < 6324 then
(if i.val < 6322 then
(if i.val < 6321 then
[1, 3, 3, 2, 2, 1, 0, 0, 3]
else
[2, 1, 0, 0, 1, 2, 2, 1, 0])
else
(if i.val < 6323 then
[2, 1, 0, 0, 1, 2, 2, 1, 3]
else
[2, 1, 0, 0, 1, 2, 2, 3, 0]))
else
(if i.val < 6326 then
(if i.val < 6325 then
[2, 1, 0, 0, 1, 2, 2, 3, 3]
else
[2, 1, 0, 0, 1, 2, 3, 0, 0])
else
(if i.val < 6327 then
[2, 1, 0, 0, 1, 2, 3, 0, 1]
else
[2, 1, 0, 0, 1, 3, 0, 2, 2])))
else
(if i.val < 6332 then
(if i.val < 6330 then
(if i.val < 6329 then
[2, 1, 0, 0, 1, 3, 2, 2, 1]
else
[2, 1, 0, 0, 1, 3, 2, 2, 3])
else
(if i.val < 6331 then
[2, 1, 0, 0, 1, 3, 3, 0, 2]
else
[2, 1, 0, 0, 3, 0, 0, 3, 2]))
else
(if i.val < 6334 then
(if i.val < 6333 then
[2, 1, 0, 0, 3, 0, 1, 2, 3]
else
[2, 1, 0, 0, 3, 3, 2, 1, 0])
else
(if i.val < 6335 then
[2, 1, 0, 3, 0, 0, 1, 1, 2]
else
[2, 1, 0, 3, 0, 0, 1, 2, 1]))))))
else
(if i.val < 6368 then
(if i.val < 6352 then
(if i.val < 6344 then
(if i.val < 6340 then
(if i.val < 6338 then
(if i.val < 6337 then
[2, 1, 0, 3, 0, 0, 1, 3, 2]
else
[2, 1, 0, 3, 0, 0, 2, 1, 0])
else
(if i.val < 6339 then
[2, 1, 0, 3, 0, 0, 2, 2, 1]
else
[2, 1, 0, 3, 0, 0, 2, 2, 3]))
else
(if i.val < 6342 then
(if i.val < 6341 then
[2, 1, 0, 3, 0, 0, 3, 2, 1]
else
[2, 1, 0, 3, 0, 1, 1, 0, 2])
else
(if i.val < 6343 then
[2, 1, 0, 3, 0, 1, 1, 2, 1]
else
[2, 1, 0, 3, 0, 1, 2, 1, 1])))
else
(if i.val < 6348 then
(if i.val < 6346 then
(if i.val < 6345 then
[2, 1, 0, 3, 0, 2, 1, 0, 0]
else
[2, 1, 0, 3, 0, 2, 1, 0, 3])
else
(if i.val < 6347 then
[2, 1, 0, 3, 0, 2, 1, 1, 0]
else
[2, 1, 0, 3, 0, 2, 1, 3, 3]))
else
(if i.val < 6350 then
(if i.val < 6349 then
[2, 1, 0, 3, 0, 2, 2, 1, 3]
else
[2, 1, 0, 3, 0, 2, 2, 3, 0])
else
(if i.val < 6351 then
[2, 1, 0, 3, 0, 2, 2, 3, 3]
else
[2, 1, 0, 3, 0, 2, 3, 3, 0]))))
else
(if i.val < 6360 then
(if i.val < 6356 then
(if i.val < 6354 then
(if i.val < 6353 then
[2, 1, 0, 3, 2, 1, 1, 0, 0]
else
[2, 1, 0, 3, 2, 1, 1, 2, 3])
else
(if i.val < 6355 then
[2, 1, 0, 3, 2, 2, 1, 1, 3]
else
[2, 1, 0, 3, 2, 2, 1, 3, 0]))
else
(if i.val < 6358 then
(if i.val < 6357 then
[2, 1, 0, 3, 2, 2, 3, 0, 0]
else
[2, 1, 0, 3, 2, 2, 3, 0, 1])
else
(if i.val < 6359 then
[2, 1, 0, 3, 3, 0, 0, 2, 1]
else
[2, 1, 0, 3, 3, 0, 0, 2, 2])))
else
(if i.val < 6364 then
(if i.val < 6362 then
(if i.val < 6361 then
[2, 1, 0, 3, 3, 0, 1, 2, 1]
else
[2, 1, 0, 3, 3, 0, 1, 2, 2])
else
(if i.val < 6363 then
[2, 1, 0, 3, 3, 0, 1, 2, 3]
else
[2, 1, 0, 3, 3, 0, 2, 2, 1]))
else
(if i.val < 6366 then
(if i.val < 6365 then
[2, 1, 0, 3, 3, 0, 2, 3, 3]
else
[2, 1, 0, 3, 3, 2, 2, 1, 1])
else
(if i.val < 6367 then
[2, 1, 1, 0, 0, 2, 1, 1, 2]
else
[2, 1, 1, 0, 0, 2, 1, 1, 3])))))
else
(if i.val < 6384 then
(if i.val < 6376 then
(if i.val < 6372 then
(if i.val < 6370 then
(if i.val < 6369 then
[2, 1, 1, 0, 0, 2, 1, 3, 3]
else
[2, 1, 1, 0, 0, 2, 3, 3, 2])
else
(if i.val < 6371 then
[2, 1, 1, 0, 0, 3, 0, 1, 2]
else
[2, 1, 1, 0, 0, 3, 2, 2, 1]))
else
(if i.val < 6374 then
(if i.val < 6373 then
[2, 1, 1, 0, 0, 3, 3, 2, 1]
else
[2, 1, 1, 0, 0, 3, 3, 2, 2])
else
(if i.val < 6375 then
[2, 1, 1, 0, 2, 1, 3, 0, 0]
else
[2, 1, 1, 0, 2, 1, 3, 0, 1])))
else
(if i.val < 6380 then
(if i.val < 6378 then
(if i.val < 6377 then
[2, 1, 1, 0, 2, 3, 0, 0, 2]
else
[2, 1, 1, 0, 2, 3, 0, 0, 3])
else
(if i.val < 6379 then
[2, 1, 1, 0, 2, 3, 0, 1, 1]
else
[2, 1, 1, 0, 2, 3, 0, 2, 1]))
else
(if i.val < 6382 then
(if i.val < 6381 then
[2, 1, 1, 0, 2, 3, 2, 1, 1]
else
[2, 1, 1, 0, 3, 0, 0, 2, 1])
else
(if i.val < 6383 then
[2, 1, 1, 0, 3, 0, 0, 2, 3]
else
[2, 1, 1, 0, 3, 0, 1, 1, 2]))))
else
(if i.val < 6392 then
(if i.val < 6388 then
(if i.val < 6386 then
(if i.val < 6385 then
[2, 1, 1, 0, 3, 0, 1, 2, 1]
else
[2, 1, 1, 0, 3, 0, 1, 2, 2])
else
(if i.val < 6387 then
[2, 1, 1, 0, 3, 0, 2, 1, 0]
else
[2, 1, 1, 0, 3, 0, 2, 1, 1]))
else
(if i.val < 6390 then
(if i.val < 6389 then
[2, 1, 1, 0, 3, 0, 2, 1, 3]
else
[2, 1, 1, 0, 3, 0, 2, 2, 3])
else
(if i.val < 6391 then
[2, 1, 1, 0, 3, 2, 1, 0, 0]
else
[2, 1, 1, 0, 3, 2, 1, 1, 0])))
else
(if i.val < 6396 then
(if i.val < 6394 then
(if i.val < 6393 then
[2, 1, 1, 0, 3, 3, 0, 1, 2]
else
[2, 1, 1, 0, 3, 3, 0, 2, 1])
else
(if i.val < 6395 then
[2, 1, 1, 0, 3, 3, 0, 2, 2]
else
[2, 1, 1, 0, 3, 3, 0, 2, 3]))
else
(if i.val < 6398 then
(if i.val < 6397 then
[2, 1, 1, 2, 3, 0, 0, 2, 3]
else
[2, 1, 1, 2, 3, 0, 2, 1, 0])
else
(if i.val < 6399 then
[2, 1, 1, 2, 3, 2, 2, 1, 3]
else
[2, 1, 1, 3, 0, 0, 1, 2, 1])))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row31_cosetWordsPart0050 : Fin 8640 → List (Fin 4) :=
  fun i => (if i.val < 6464 then
(if i.val < 6432 then
(if i.val < 6416 then
(if i.val < 6408 then
(if i.val < 6404 then
(if i.val < 6402 then
(if i.val < 6401 then
[2, 1, 1, 3, 0, 0, 3, 2, 1]
else
[2, 1, 1, 3, 0, 0, 3, 2, 2])
else
(if i.val < 6403 then
[2, 1, 1, 3, 0, 1, 1, 2, 1]
else
[2, 1, 1, 3, 0, 1, 1, 2, 2]))
else
(if i.val < 6406 then
(if i.val < 6405 then
[2, 1, 1, 3, 0, 1, 2, 2, 1]
else
[2, 1, 1, 3, 0, 1, 2, 2, 3])
else
(if i.val < 6407 then
[2, 1, 1, 3, 0, 2, 1, 1, 2]
else
[2, 1, 1, 3, 0, 2, 2, 1, 1])))
else
(if i.val < 6412 then
(if i.val < 6410 then
(if i.val < 6409 then
[2, 1, 1, 3, 0, 2, 2, 3, 0]
else
[2, 1, 1, 3, 0, 2, 3, 3, 2])
else
(if i.val < 6411 then
[2, 1, 1, 3, 2, 1, 0, 0, 3]
else
[2, 1, 1, 3, 2, 1, 0, 3, 2]))
else
(if i.val < 6414 then
(if i.val < 6413 then
[2, 1, 1, 3, 2, 1, 1, 0, 0]
else
[2, 1, 1, 3, 2, 2, 1, 0, 0])
else
(if i.val < 6415 then
[2, 1, 1, 3, 2, 2, 1, 1, 3]
else
[2, 1, 1, 3, 2, 2, 1, 3, 0]))))
else
(if i.val < 6424 then
(if i.val < 6420 then
(if i.val < 6418 then
(if i.val < 6417 then
[2, 1, 1, 3, 2, 2, 3, 0, 1]
else
[2, 1, 1, 3, 3, 0, 0, 2, 3])
else
(if i.val < 6419 then
[2, 1, 1, 3, 3, 0, 1, 2, 1]
else
[2, 1, 1, 3, 3, 0, 1, 2, 3]))
else
(if i.val < 6422 then
(if i.val < 6421 then
[2, 1, 1, 3, 3, 2, 1, 0, 0]
else
[2, 1, 1, 3, 3, 2, 1, 0, 3])
else
(if i.val < 6423 then
[2, 1, 3, 0, 0, 1, 2, 1, 1]
else
[2, 1, 3, 0, 0, 1, 2, 1, 3])))
else
(if i.val < 6428 then
(if i.val < 6426 then
(if i.val < 6425 then
[2, 1, 3, 0, 0, 1, 2, 2, 3]
else
[2, 1, 3, 0, 0, 1, 2, 3, 3])
else
(if i.val < 6427 then
[2, 1, 3, 0, 0, 2, 1, 1, 2]
else
[2, 1, 3, 0, 0, 2, 3, 2, 1]))
else
(if i.val < 6430 then
(if i.val < 6429 then
[2, 1, 3, 0, 0, 2, 3, 3, 2]
else
[2, 1, 3, 0, 0, 3, 2, 1, 1])
else
(if i.val < 6431 then
[2, 1, 3, 0, 0, 3, 2, 2, 1]
else
[2, 1, 3, 0, 1, 2, 1, 1, 2])))))
else
(if i.val < 6448 then
(if i.val < 6440 then
(if i.val < 6436 then
(if i.val < 6434 then
(if i.val < 6433 then
[2, 1, 3, 0, 1, 2, 1, 3, 0]
else
[2, 1, 3, 0, 1, 2, 2, 1, 0])
else
(if i.val < 6435 then
[2, 1, 3, 0, 1, 2, 2, 1, 1]
else
[2, 1, 3, 0, 1, 2, 2, 1, 3]))
else
(if i.val < 6438 then
(if i.val < 6437 then
[2, 1, 3, 0, 1, 2, 2, 3, 0]
else
[2, 1, 3, 0, 1, 2, 3, 0, 1])
else
(if i.val < 6439 then
[2, 1, 3, 0, 1, 2, 3, 3, 0]
else
[2, 1, 3, 0, 2, 1, 1, 0, 2])))
else
(if i.val < 6444 then
(if i.val < 6442 then
(if i.val < 6441 then
[2, 1, 3, 0, 2, 3, 3, 0, 2]
else
[2, 1, 3, 0, 2, 3, 3, 2, 1])
else
(if i.val < 6443 then
[2, 1, 3, 2, 1, 0, 3, 2, 1]
else
[2, 1, 3, 2, 1, 0, 3, 3, 2]))
else
(if i.val < 6446 then
(if i.val < 6445 then
[2, 1, 3, 3, 0, 0, 1, 1, 2]
else
[2, 1, 3, 3, 0, 0, 1, 2, 2])
else
(if i.val < 6447 then
[2, 1, 3, 3, 0, 0, 1, 2, 3]
else
[2, 1, 3, 3, 0, 0, 2, 1, 1]))))
else
(if i.val < 6456 then
(if i.val < 6452 then
(if i.val < 6450 then
(if i.val < 6449 then
[2, 1, 3, 3, 0, 0, 2, 2, 1]
else
[2, 1, 3, 3, 0, 0, 2, 2, 3])
else
(if i.val < 6451 then
[2, 1, 3, 3, 0, 1, 1, 0, 2]
else
[2, 1, 3, 3, 0, 1, 2, 1, 0]))
else
(if i.val < 6454 then
(if i.val < 6453 then
[2, 1, 3, 3, 0, 1, 2, 1, 1]
else
[2, 1, 3, 3, 0, 1, 2, 2, 1])
else
(if i.val < 6455 then
[2, 1, 3, 3, 0, 1, 2, 2, 3]
else
[2, 1, 3, 3, 0, 1, 2, 3, 0])))
else
(if i.val < 6460 then
(if i.val < 6458 then
(if i.val < 6457 then
[2, 1, 3, 3, 0, 2, 1, 1, 0]
else
[2, 1, 3, 3, 0, 2, 1, 1, 2])
else
(if i.val < 6459 then
[2, 1, 3, 3, 0, 2, 2, 1, 0]
else
[2, 1, 3, 3, 0, 2, 2, 1, 3]))
else
(if i.val < 6462 then
(if i.val < 6461 then
[2, 2, 1, 0, 0, 1, 2, 3, 3]
else
[2, 2, 1, 0, 0, 1, 3, 0, 2])
else
(if i.val < 6463 then
[2, 2, 1, 0, 0, 3, 2, 2, 1]
else
[2, 2, 1, 0, 0, 3, 2, 2, 3]))))))
else
(if i.val < 6496 then
(if i.val < 6480 then
(if i.val < 6472 then
(if i.val < 6468 then
(if i.val < 6466 then
(if i.val < 6465 then
[2, 2, 1, 0, 0, 3, 3, 2, 1]
else
[2, 2, 1, 0, 0, 3, 3, 2, 2])
else
(if i.val < 6467 then
[2, 2, 1, 0, 3, 0, 0, 2, 1]
else
[2, 2, 1, 0, 3, 0, 0, 3, 2]))
else
(if i.val < 6470 then
(if i.val < 6469 then
[2, 2, 1, 0, 3, 0, 2, 1, 0]
else
[2, 2, 1, 0, 3, 0, 2, 3, 3])
else
(if i.val < 6471 then
[2, 2, 1, 0, 3, 2, 1, 0, 0]
else
[2, 2, 1, 0, 3, 2, 1, 1, 0])))
else
(if i.val < 6476 then
(if i.val < 6474 then
(if i.val < 6473 then
[2, 2, 1, 0, 3, 3, 0, 1, 2]
else
[2, 2, 1, 1, 0, 0, 3, 3, 2])
else
(if i.val < 6475 then
[2, 2, 1, 1, 0, 3, 0, 0, 2]
else
[2, 2, 1, 1, 0, 3, 0, 2, 1]))
else
(if i.val < 6478 then
(if i.val < 6477 then
[2, 2, 1, 1, 0, 3, 0, 2, 3]
else
[2, 2, 1, 1, 0, 3, 2, 1, 0])
else
(if i.val < 6479 then
[2, 2, 1, 1, 0, 3, 2, 1, 1]
else
[2, 2, 1, 1, 0, 3, 2, 2, 3]))))
else
(if i.val < 6488 then
(if i.val < 6484 then
(if i.val < 6482 then
(if i.val < 6481 then
[2, 2, 1, 1, 3, 0, 1, 2, 1]
else
[2, 2, 1, 1, 3, 0, 1, 2, 3])
else
(if i.val < 6483 then
[2, 2, 1, 1, 3, 0, 2, 1, 0]
else
[2, 2, 1, 1, 3, 2, 1, 0, 0]))
else
(if i.val < 6486 then
(if i.val < 6485 then
[2, 2, 1, 1, 3, 3, 0, 1, 2]
else
[2, 2, 1, 3, 0, 0, 1, 2, 2])
else
(if i.val < 6487 then
[2, 2, 1, 3, 0, 0, 1, 2, 3]
else
[2, 2, 1, 3, 0, 0, 2, 1, 0])))
else
(if i.val < 6492 then
(if i.val < 6490 then
(if i.val < 6489 then
[2, 2, 1, 3, 0, 0, 3, 2, 1]
else
[2, 2, 1, 3, 0, 0, 3, 2, 2])
else
(if i.val < 6491 then
[2, 2, 1, 3, 0, 1, 2, 1, 1]
else
[2, 2, 1, 3, 0, 1, 2, 3, 0]))
else
(if i.val < 6494 then
(if i.val < 6493 then
[2, 2, 1, 3, 0, 1, 2, 3, 3]
else
[2, 2, 1, 3, 0, 2, 1, 1, 2])
else
(if i.val < 6495 then
[2, 2, 1, 3, 2, 1, 0, 0, 3]
else
[2, 2, 1, 3, 2, 1, 1, 0, 0])))))
else
(if i.val < 6512 then
(if i.val < 6504 then
(if i.val < 6500 then
(if i.val < 6498 then
(if i.val < 6497 then
[2, 2, 1, 3, 3, 0, 0, 1, 2]
else
[2, 2, 1, 3, 3, 0, 0, 2, 3])
else
(if i.val < 6499 then
[2, 2, 1, 3, 3, 0, 1, 2, 1]
else
[2, 2, 1, 3, 3, 0, 1, 2, 3]))
else
(if i.val < 6502 then
(if i.val < 6501 then
[2, 2, 1, 3, 3, 0, 2, 1, 1]
else
[2, 2, 1, 3, 3, 2, 1, 0, 0])
else
(if i.val < 6503 then
[2, 2, 1, 3, 3, 2, 1, 0, 3]
else
[2, 2, 3, 0, 0, 1, 1, 2, 2])))
else
(if i.val < 6508 then
(if i.val < 6506 then
(if i.val < 6505 then
[2, 2, 3, 0, 0, 1, 2, 2, 1]
else
[2, 2, 3, 0, 0, 1, 2, 2, 3])
else
(if i.val < 6507 then
[2, 2, 3, 0, 0, 2, 1, 1, 2]
else
[2, 2, 3, 0, 0, 2, 2, 3, 0]))
else
(if i.val < 6510 then
(if i.val < 6509 then
[2, 2, 3, 0, 0, 2, 3, 2, 1]
else
[2, 2, 3, 0, 0, 2, 3, 3, 2])
else
(if i.val < 6511 then
[2, 2, 3, 0, 0, 3, 2, 1, 0]
else
[2, 2, 3, 0, 0, 3, 2, 1, 1]))))
else
(if i.val < 6520 then
(if i.val < 6516 then
(if i.val < 6514 then
(if i.val < 6513 then
[2, 2, 3, 0, 1, 1, 0, 3, 2]
else
[2, 2, 3, 0, 1, 2, 1, 1, 0])
else
(if i.val < 6515 then
[2, 2, 3, 0, 1, 2, 1, 1, 3]
else
[2, 2, 3, 0, 1, 2, 1, 3, 0]))
else
(if i.val < 6518 then
(if i.val < 6517 then
[2, 2, 3, 0, 1, 2, 1, 3, 3]
else
[2, 2, 3, 0, 1, 2, 3, 0, 1])
else
(if i.val < 6519 then
[2, 2, 3, 0, 1, 2, 3, 3, 0]
else
[2, 2, 3, 0, 1, 2, 3, 3, 2])))
else
(if i.val < 6524 then
(if i.val < 6522 then
(if i.val < 6521 then
[2, 2, 3, 0, 2, 1, 1, 0, 2]
else
[2, 2, 3, 0, 2, 2, 1, 0, 3])
else
(if i.val < 6523 then
[2, 2, 3, 0, 2, 2, 1, 1, 3]
else
[2, 2, 3, 0, 2, 3, 3, 0, 2]))
else
(if i.val < 6526 then
(if i.val < 6525 then
[2, 2, 3, 0, 2, 3, 3, 2, 1]
else
[2, 2, 3, 2, 1, 0, 3, 2, 1])
else
(if i.val < 6527 then
[2, 2, 3, 2, 1, 0, 3, 2, 2]
else
[2, 2, 3, 2, 2, 1, 0, 3, 0])))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row31_cosetWordsPart0051 : Fin 8640 → List (Fin 4) :=
  fun i => (if i.val < 6592 then
(if i.val < 6560 then
(if i.val < 6544 then
(if i.val < 6536 then
(if i.val < 6532 then
(if i.val < 6530 then
(if i.val < 6529 then
[2, 2, 3, 2, 2, 1, 3, 0, 0]
else
[2, 2, 3, 2, 2, 3, 0, 1, 1])
else
(if i.val < 6531 then
[2, 2, 3, 2, 2, 3, 0, 1, 2]
else
[2, 2, 3, 3, 0, 0, 1, 1, 2]))
else
(if i.val < 6534 then
(if i.val < 6533 then
[2, 2, 3, 3, 0, 1, 2, 1, 0]
else
[2, 2, 3, 3, 0, 1, 2, 1, 1])
else
(if i.val < 6535 then
[2, 2, 3, 3, 0, 1, 2, 1, 3]
else
[2, 2, 3, 3, 0, 1, 2, 3, 0])))
else
(if i.val < 6540 then
(if i.val < 6538 then
(if i.val < 6537 then
[2, 2, 3, 3, 0, 2, 1, 1, 3]
else
[2, 2, 3, 3, 0, 2, 2, 1, 1])
else
(if i.val < 6539 then
[2, 2, 3, 3, 0, 2, 3, 3, 2]
else
[2, 3, 0, 0, 1, 1, 2, 1, 1]))
else
(if i.val < 6542 then
(if i.val < 6541 then
[2, 3, 0, 0, 1, 1, 2, 1, 3]
else
[2, 3, 0, 0, 1, 1, 2, 2, 1])
else
(if i.val < 6543 then
[2, 3, 0, 0, 1, 1, 2, 3, 3]
else
[2, 3, 0, 0, 1, 2, 2, 3, 0]))))
else
(if i.val < 6552 then
(if i.val < 6548 then
(if i.val < 6546 then
(if i.val < 6545 then
[2, 3, 0, 0, 1, 2, 3, 0, 1]
else
[2, 3, 0, 0, 1, 3, 2, 2, 1])
else
(if i.val < 6547 then
[2, 3, 0, 0, 2, 2, 3, 0, 0]
else
[2, 3, 0, 0, 2, 2, 3, 3, 2]))
else
(if i.val < 6550 then
(if i.val < 6549 then
[2, 3, 0, 0, 2, 3, 2, 1, 1]
else
[2, 3, 0, 0, 2, 3, 3, 2, 1])
else
(if i.val < 6551 then
[2, 3, 0, 0, 3, 2, 1, 0, 0]
else
[2, 3, 0, 0, 3, 2, 1, 1, 0])))
else
(if i.val < 6556 then
(if i.val < 6554 then
(if i.val < 6553 then
[2, 3, 0, 0, 3, 2, 1, 1, 2]
else
[2, 3, 0, 0, 3, 2, 2, 1, 3])
else
(if i.val < 6555 then
[2, 3, 0, 0, 3, 2, 2, 3, 0]
else
[2, 3, 0, 1, 1, 0, 2, 3, 2]))
else
(if i.val < 6558 then
(if i.val < 6557 then
[2, 3, 0, 1, 1, 0, 2, 3, 3]
else
[2, 3, 0, 1, 1, 0, 3, 2, 1])
else
(if i.val < 6559 then
[2, 3, 0, 1, 1, 2, 1, 0, 3]
else
[2, 3, 0, 1, 1, 2, 2, 1, 1])))))
else
(if i.val < 6576 then
(if i.val < 6568 then
(if i.val < 6564 then
(if i.val < 6562 then
(if i.val < 6561 then
[2, 3, 0, 1, 1, 2, 2, 3, 0]
else
[2, 3, 0, 1, 1, 2, 2, 3, 3])
else
(if i.val < 6563 then
[2, 3, 0, 1, 1, 2, 3, 0, 1]
else
[2, 3, 0, 1, 1, 2, 3, 3, 0]))
else
(if i.val < 6566 then
(if i.val < 6565 then
[2, 3, 0, 1, 2, 1, 0, 3, 2]
else
[2, 3, 0, 1, 2, 1, 1, 0, 2])
else
(if i.val < 6567 then
[2, 3, 0, 1, 2, 1, 1, 0, 3]
else
[2, 3, 0, 1, 2, 1, 1, 2, 3])))
else
(if i.val < 6572 then
(if i.val < 6570 then
(if i.val < 6569 then
[2, 3, 0, 1, 2, 1, 1, 3, 2]
else
[2, 3, 0, 1, 2, 1, 1, 3, 3])
else
(if i.val < 6571 then
[2, 3, 0, 1, 2, 1, 3, 0, 1]
else
[2, 3, 0, 1, 2, 1, 3, 2, 2]))
else
(if i.val < 6574 then
(if i.val < 6573 then
[2, 3, 0, 1, 2, 1, 3, 3, 2]
else
[2, 3, 0, 1, 2, 2, 1, 0, 0])
else
(if i.val < 6575 then
[2, 3, 0, 1, 2, 2, 1, 3, 3]
else
[2, 3, 0, 1, 2, 2, 3, 0, 0]))))
else
(if i.val < 6584 then
(if i.val < 6580 then
(if i.val < 6578 then
(if i.val < 6577 then
[2, 3, 0, 1, 2, 2, 3, 3, 0]
else
[2, 3, 0, 1, 2, 3, 3, 2, 1])
else
(if i.val < 6579 then
[2, 3, 0, 2, 1, 1, 0, 2, 1]
else
[2, 3, 0, 2, 1, 1, 2, 3, 0]))
else
(if i.val < 6582 then
(if i.val < 6581 then
[2, 3, 0, 2, 1, 1, 2, 3, 2]
else
[2, 3, 0, 2, 1, 1, 2, 3, 3])
else
(if i.val < 6583 then
[2, 3, 0, 2, 1, 1, 3, 2, 2]
else
[2, 3, 0, 2, 1, 3, 2, 2, 1])))
else
(if i.val < 6588 then
(if i.val < 6586 then
(if i.val < 6585 then
[2, 3, 0, 2, 1, 3, 2, 2, 3]
else
[2, 3, 0, 2, 1, 3, 3, 0, 1])
else
(if i.val < 6587 then
[2, 3, 0, 2, 1, 3, 3, 0, 2]
else
[2, 3, 0, 2, 1, 3, 3, 2, 1]))
else
(if i.val < 6590 then
(if i.val < 6589 then
[2, 3, 0, 2, 2, 1, 0, 3, 0]
else
[2, 3, 0, 2, 2, 1, 1, 3, 3])
else
(if i.val < 6591 then
[2, 3, 0, 2, 2, 1, 3, 0, 2]
else
[2, 3, 0, 2, 2, 1, 3, 3, 2]))))))
else
(if i.val < 6624 then
(if i.val < 6608 then
(if i.val < 6600 then
(if i.val < 6596 then
(if i.val < 6594 then
(if i.val < 6593 then
[2, 3, 0, 2, 2, 3, 0, 1, 1]
else
[2, 3, 0, 2, 3, 3, 2, 1, 0])
else
(if i.val < 6595 then
[2, 3, 0, 2, 3, 3, 2, 1, 1]
else
[2, 3, 2, 1, 0, 0, 1, 2, 2]))
else
(if i.val < 6598 then
(if i.val < 6597 then
[2, 3, 2, 1, 0, 0, 3, 2, 1]
else
[2, 3, 2, 1, 0, 0, 3, 2, 2])
else
(if i.val < 6599 then
[2, 3, 2, 1, 0, 3, 2, 1, 1]
else
[2, 3, 2, 1, 0, 3, 2, 2, 1])))
else
(if i.val < 6604 then
(if i.val < 6602 then
(if i.val < 6601 then
[2, 3, 2, 1, 0, 3, 2, 2, 3]
else
[2, 3, 2, 1, 1, 0, 2, 3, 2])
else
(if i.val < 6603 then
[2, 3, 2, 1, 1, 0, 3, 2, 1]
else
[2, 3, 2, 1, 1, 0, 3, 3, 2]))
else
(if i.val < 6606 then
(if i.val < 6605 then
[2, 3, 2, 2, 1, 0, 0, 1, 2]
else
[2, 3, 2, 2, 1, 0, 3, 2, 1])
else
(if i.val < 6607 then
[2, 3, 2, 2, 1, 0, 3, 2, 2]
else
[2, 3, 2, 2, 1, 1, 0, 3, 2]))))
else
(if i.val < 6616 then
(if i.val < 6612 then
(if i.val < 6610 then
(if i.val < 6609 then
[2, 3, 2, 2, 1, 1, 0, 3, 3]
else
[2, 3, 2, 2, 1, 3, 0, 1, 2])
else
(if i.val < 6611 then
[2, 3, 2, 2, 1, 3, 2, 2, 1]
else
[2, 3, 2, 2, 3, 0, 0, 3, 2]))
else
(if i.val < 6614 then
(if i.val < 6613 then
[2, 3, 2, 2, 3, 0, 1, 1, 2]
else
[2, 3, 2, 2, 3, 0, 1, 2, 3])
else
(if i.val < 6615 then
[2, 3, 3, 0, 0, 1, 1, 2, 2]
else
[2, 3, 3, 0, 0, 1, 1, 2, 3])))
else
(if i.val < 6620 then
(if i.val < 6618 then
(if i.val < 6617 then
[2, 3, 3, 0, 0, 2, 1, 3, 3]
else
[2, 3, 3, 0, 1, 1, 0, 2, 1])
else
(if i.val < 6619 then
[2, 3, 3, 0, 1, 1, 0, 2, 2]
else
[2, 3, 3, 0, 1, 1, 0, 2, 3]))
else
(if i.val < 6622 then
(if i.val < 6621 then
[2, 3, 3, 0, 1, 1, 0, 3, 2]
else
[2, 3, 3, 0, 1, 1, 2, 2, 1])
else
(if i.val < 6623 then
[2, 3, 3, 0, 1, 1, 2, 2, 3]
else
[2, 3, 3, 0, 1, 2, 1, 0, 0])))))
else
(if i.val < 6640 then
(if i.val < 6632 then
(if i.val < 6628 then
(if i.val < 6626 then
(if i.val < 6625 then
[2, 3, 3, 0, 1, 2, 1, 1, 0]
else
[2, 3, 3, 0, 1, 2, 1, 1, 3])
else
(if i.val < 6627 then
[2, 3, 3, 0, 1, 2, 1, 3, 0]
else
[2, 3, 3, 0, 1, 2, 1, 3, 3]))
else
(if i.val < 6630 then
(if i.val < 6629 then
[2, 3, 3, 0, 1, 2, 2, 1, 0]
else
[2, 3, 3, 0, 1, 2, 2, 1, 1])
else
(if i.val < 6631 then
[2, 3, 3, 0, 1, 2, 3, 0, 0]
else
[2, 3, 3, 0, 2, 1, 0, 3, 0])))
else
(if i.val < 6636 then
(if i.val < 6634 then
(if i.val < 6633 then
[2, 3, 3, 0, 2, 1, 1, 3, 2]
else
[2, 3, 3, 0, 2, 1, 3, 0, 0])
else
(if i.val < 6635 then
[2, 3, 3, 0, 2, 2, 1, 0, 3]
else
[2, 3, 3, 0, 2, 2, 1, 1, 3]))
else
(if i.val < 6638 then
(if i.val < 6637 then
[2, 3, 3, 0, 2, 2, 1, 3, 0]
else
[2, 3, 3, 0, 2, 2, 1, 3, 3])
else
(if i.val < 6639 then
[2, 3, 3, 0, 2, 2, 3, 3, 0]
else
[2, 3, 3, 0, 2, 3, 3, 0, 2]))))
else
(if i.val < 6648 then
(if i.val < 6644 then
(if i.val < 6642 then
(if i.val < 6641 then
[2, 3, 3, 0, 2, 3, 3, 2, 1]
else
[2, 3, 3, 2, 1, 0, 0, 1, 3])
else
(if i.val < 6643 then
[2, 3, 3, 2, 1, 0, 3, 2, 2]
else
[2, 3, 3, 2, 2, 1, 1, 0, 0]))
else
(if i.val < 6646 then
(if i.val < 6645 then
[2, 3, 3, 2, 2, 1, 1, 0, 3]
else
[3, 0, 0, 1, 1, 2, 1, 0, 0])
else
(if i.val < 6647 then
[3, 0, 0, 1, 1, 2, 1, 1, 2]
else
[3, 0, 0, 1, 1, 2, 1, 3, 3])))
else
(if i.val < 6652 then
(if i.val < 6650 then
(if i.val < 6649 then
[3, 0, 0, 1, 1, 2, 2, 1, 0]
else
[3, 0, 0, 1, 1, 2, 2, 1, 1])
else
(if i.val < 6651 then
[3, 0, 0, 1, 1, 2, 2, 1, 3]
else
[3, 0, 0, 1, 1, 2, 3, 0, 1]))
else
(if i.val < 6654 then
(if i.val < 6653 then
[3, 0, 0, 1, 1, 2, 3, 3, 2]
else
[3, 0, 0, 1, 2, 1, 0, 3, 0])
else
(if i.val < 6655 then
[3, 0, 0, 1, 2, 1, 1, 2, 3]
else
[3, 0, 0, 1, 2, 1, 1, 3, 0])))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row31_cosetWordsPart0052 : Fin 8640 → List (Fin 4) :=
  fun i => (if i.val < 6720 then
(if i.val < 6688 then
(if i.val < 6672 then
(if i.val < 6664 then
(if i.val < 6660 then
(if i.val < 6658 then
(if i.val < 6657 then
[3, 0, 0, 1, 2, 2, 1, 1, 3]
else
[3, 0, 0, 1, 2, 2, 1, 3, 3])
else
(if i.val < 6659 then
[3, 0, 0, 1, 2, 2, 3, 0, 0]
else
[3, 0, 0, 1, 2, 2, 3, 0, 1]))
else
(if i.val < 6662 then
(if i.val < 6661 then
[3, 0, 0, 1, 2, 2, 3, 2, 1]
else
[3, 0, 0, 1, 2, 2, 3, 2, 2])
else
(if i.val < 6663 then
[3, 0, 0, 1, 2, 3, 0, 0, 2]
else
[3, 0, 0, 1, 2, 3, 3, 2, 1])))
else
(if i.val < 6668 then
(if i.val < 6666 then
(if i.val < 6665 then
[3, 0, 0, 1, 3, 0, 2, 1, 1]
else
[3, 0, 0, 1, 3, 2, 1, 1, 2])
else
(if i.val < 6667 then
[3, 0, 0, 2, 1, 0, 3, 2, 2]
else
[3, 0, 0, 2, 1, 1, 2, 3, 0]))
else
(if i.val < 6670 then
(if i.val < 6669 then
[3, 0, 0, 2, 1, 1, 2, 3, 2]
else
[3, 0, 0, 2, 1, 1, 2, 3, 3])
else
(if i.val < 6671 then
[3, 0, 0, 2, 1, 1, 3, 2, 2]
else
[3, 0, 0, 2, 2, 1, 0, 3, 0]))))
else
(if i.val < 6680 then
(if i.val < 6676 then
(if i.val < 6674 then
(if i.val < 6673 then
[3, 0, 0, 2, 2, 1, 1, 3, 2]
else
[3, 0, 0, 2, 2, 1, 3, 0, 0])
else
(if i.val < 6675 then
[3, 0, 0, 2, 2, 1, 3, 3, 2]
else
[3, 0, 0, 2, 2, 3, 0, 1, 2]))
else
(if i.val < 6678 then
(if i.val < 6677 then
[3, 0, 0, 2, 2, 3, 0, 2, 2]
else
[3, 0, 0, 2, 2, 3, 2, 1, 0])
else
(if i.val < 6679 then
[3, 0, 0, 2, 2, 3, 2, 1, 1]
else
[3, 0, 0, 2, 2, 3, 2, 2, 1])))
else
(if i.val < 6684 then
(if i.val < 6682 then
(if i.val < 6681 then
[3, 0, 0, 2, 3, 2, 1, 0, 0]
else
[3, 0, 0, 2, 3, 2, 1, 1, 2])
else
(if i.val < 6683 then
[3, 0, 0, 2, 3, 3, 2, 1, 0]
else
[3, 0, 0, 2, 3, 3, 2, 1, 1]))
else
(if i.val < 6686 then
(if i.val < 6685 then
[3, 0, 0, 3, 2, 1, 1, 0, 2]
else
[3, 0, 0, 3, 2, 1, 1, 2, 3])
else
(if i.val < 6687 then
[3, 0, 0, 3, 2, 2, 1, 1, 0]
else
[3, 0, 0, 3, 2, 2, 1, 1, 3])))))
else
(if i.val < 6704 then
(if i.val < 6696 then
(if i.val < 6692 then
(if i.val < 6690 then
(if i.val < 6689 then
[3, 0, 0, 3, 2, 2, 1, 3, 0]
else
[3, 0, 0, 3, 2, 2, 1, 3, 2])
else
(if i.val < 6691 then
[3, 0, 0, 3, 2, 2, 3, 0, 0]
else
[3, 0, 1, 1, 0, 2, 1, 0, 0]))
else
(if i.val < 6694 then
(if i.val < 6693 then
[3, 0, 1, 1, 0, 2, 1, 1, 2]
else
[3, 0, 1, 1, 0, 2, 2, 1, 0])
else
(if i.val < 6695 then
[3, 0, 1, 1, 0, 2, 2, 3, 2]
else
[3, 0, 1, 1, 0, 2, 2, 3, 3])))
else
(if i.val < 6700 then
(if i.val < 6698 then
(if i.val < 6697 then
[3, 0, 1, 1, 0, 3, 2, 1, 1]
else
[3, 0, 1, 1, 0, 3, 2, 2, 1])
else
(if i.val < 6699 then
[3, 0, 1, 1, 0, 3, 3, 0, 2]
else
[3, 0, 1, 1, 2, 2, 3, 3, 0]))
else
(if i.val < 6702 then
(if i.val < 6701 then
[3, 0, 1, 1, 2, 3, 3, 0, 1]
else
[3, 0, 1, 2, 1, 0, 3, 0, 0])
else
(if i.val < 6703 then
[3, 0, 1, 2, 1, 0, 3, 0, 1]
else
[3, 0, 1, 2, 1, 1, 0, 0, 2]))))
else
(if i.val < 6712 then
(if i.val < 6708 then
(if i.val < 6706 then
(if i.val < 6705 then
[3, 0, 1, 2, 1, 1, 0, 2, 1]
else
[3, 0, 1, 2, 1, 1, 0, 2, 3])
else
(if i.val < 6707 then
[3, 0, 1, 2, 1, 1, 0, 3, 2]
else
[3, 0, 1, 2, 1, 1, 3, 0, 1]))
else
(if i.val < 6710 then
(if i.val < 6709 then
[3, 0, 1, 2, 1, 3, 0, 1, 1]
else
[3, 0, 1, 2, 1, 3, 0, 1, 2])
else
(if i.val < 6711 then
[3, 0, 1, 2, 1, 3, 0, 2, 1]
else
[3, 0, 1, 2, 1, 3, 0, 2, 2])))
else
(if i.val < 6716 then
(if i.val < 6714 then
(if i.val < 6713 then
[3, 0, 1, 2, 1, 3, 2, 2, 1]
else
[3, 0, 1, 2, 1, 3, 3, 2, 1])
else
(if i.val < 6715 then
[3, 0, 1, 2, 1, 3, 3, 2, 2]
else
[3, 0, 1, 2, 2, 1, 1, 3, 2]))
else
(if i.val < 6718 then
(if i.val < 6717 then
[3, 0, 1, 2, 2, 1, 1, 3, 3]
else
[3, 0, 1, 2, 2, 1, 3, 3, 2])
else
(if i.val < 6719 then
[3, 0, 1, 2, 2, 3, 3, 0, 0]
else
[3, 0, 1, 2, 3, 0, 1, 1, 2]))))))
else
(if i.val < 6752 then
(if i.val < 6736 then
(if i.val < 6728 then
(if i.val < 6724 then
(if i.val < 6722 then
(if i.val < 6721 then
[3, 0, 1, 2, 3, 3, 0, 0, 2]
else
[3, 0, 1, 2, 3, 3, 0, 1, 2])
else
(if i.val < 6723 then
[3, 0, 1, 2, 3, 3, 2, 1, 1]
else
[3, 0, 2, 1, 0, 3, 2, 2, 1]))
else
(if i.val < 6726 then
(if i.val < 6725 then
[3, 0, 2, 1, 0, 3, 2, 2, 3]
else
[3, 0, 2, 1, 0, 3, 3, 0, 1])
else
(if i.val < 6727 then
[3, 0, 2, 1, 0, 3, 3, 2, 1]
else
[3, 0, 2, 1, 1, 0, 0, 2, 1])))
else
(if i.val < 6732 then
(if i.val < 6730 then
(if i.val < 6729 then
[3, 0, 2, 1, 1, 0, 0, 2, 3]
else
[3, 0, 2, 1, 1, 0, 2, 1, 1])
else
(if i.val < 6731 then
[3, 0, 2, 1, 1, 0, 2, 1, 3]
else
[3, 0, 2, 1, 1, 0, 2, 3, 2]))
else
(if i.val < 6734 then
(if i.val < 6733 then
[3, 0, 2, 1, 1, 0, 2, 3, 3]
else
[3, 0, 2, 1, 1, 0, 3, 0, 2])
else
(if i.val < 6735 then
[3, 0, 2, 1, 1, 0, 3, 2, 1]
else
[3, 0, 2, 1, 1, 0, 3, 2, 2]))))
else
(if i.val < 6744 then
(if i.val < 6740 then
(if i.val < 6738 then
(if i.val < 6737 then
[3, 0, 2, 1, 1, 0, 3, 3, 2]
else
[3, 0, 2, 1, 1, 2, 3, 0, 0])
else
(if i.val < 6739 then
[3, 0, 2, 1, 1, 2, 3, 0, 1]
else
[3, 0, 2, 1, 1, 2, 3, 3, 0]))
else
(if i.val < 6742 then
(if i.val < 6741 then
[3, 0, 2, 1, 1, 3, 2, 2, 3]
else
[3, 0, 2, 1, 3, 3, 0, 1, 2])
else
(if i.val < 6743 then
[3, 0, 2, 1, 3, 3, 0, 2, 2]
else
[3, 0, 2, 1, 3, 3, 2, 1, 0])))
else
(if i.val < 6748 then
(if i.val < 6746 then
(if i.val < 6745 then
[3, 0, 2, 1, 3, 3, 2, 2, 1]
else
[3, 0, 2, 2, 1, 0, 3, 0, 1])
else
(if i.val < 6747 then
[3, 0, 2, 2, 1, 0, 3, 0, 2]
else
[3, 0, 2, 2, 1, 0, 3, 2, 1]))
else
(if i.val < 6750 then
(if i.val < 6749 then
[3, 0, 2, 2, 1, 1, 3, 0, 1]
else
[3, 0, 2, 2, 1, 3, 0, 0, 2])
else
(if i.val < 6751 then
[3, 0, 2, 2, 1, 3, 3, 0, 1]
else
[3, 0, 2, 2, 3, 0, 1, 2, 3])))))
else
(if i.val < 6768 then
(if i.val < 6760 then
(if i.val < 6756 then
(if i.val < 6754 then
(if i.val < 6753 then
[3, 0, 2, 3, 3, 0, 1, 1, 2]
else
[3, 0, 2, 3, 3, 0, 1, 2, 3])
else
(if i.val < 6755 then
[3, 0, 2, 3, 3, 0, 2, 1, 1]
else
[3, 0, 2, 3, 3, 0, 2, 1, 3]))
else
(if i.val < 6758 then
(if i.val < 6757 then
[3, 0, 2, 3, 3, 2, 1, 0, 0]
else
[3, 2, 1, 0, 0, 1, 2, 3, 3])
else
(if i.val < 6759 then
[3, 2, 1, 0, 0, 1, 3, 2, 2]
else
[3, 2, 1, 0, 0, 3, 2, 2, 1])))
else
(if i.val < 6764 then
(if i.val < 6762 then
(if i.val < 6761 then
[3, 2, 1, 0, 3, 2, 1, 0, 0]
else
[3, 2, 1, 0, 3, 2, 2, 1, 0])
else
(if i.val < 6763 then
[3, 2, 1, 0, 3, 2, 2, 1, 3]
else
[3, 2, 1, 0, 3, 3, 0, 2, 2]))
else
(if i.val < 6766 then
(if i.val < 6765 then
[3, 2, 1, 0, 3, 3, 2, 1, 0]
else
[3, 2, 1, 1, 0, 0, 2, 3, 0])
else
(if i.val < 6767 then
[3, 2, 1, 1, 0, 0, 3, 3, 2]
else
[3, 2, 1, 1, 0, 2, 1, 1, 2]))))
else
(if i.val < 6776 then
(if i.val < 6772 then
(if i.val < 6770 then
(if i.val < 6769 then
[3, 2, 1, 1, 0, 2, 1, 1, 3]
else
[3, 2, 1, 1, 0, 2, 1, 3, 3])
else
(if i.val < 6771 then
[3, 2, 1, 1, 0, 2, 3, 0, 2]
else
[3, 2, 1, 1, 0, 2, 3, 2, 1]))
else
(if i.val < 6774 then
(if i.val < 6773 then
[3, 2, 1, 1, 0, 2, 3, 3, 2]
else
[3, 2, 1, 1, 0, 3, 2, 1, 0])
else
(if i.val < 6775 then
[3, 2, 1, 1, 2, 3, 3, 2, 1]
else
[3, 2, 2, 1, 0, 0, 1, 2, 3])))
else
(if i.val < 6780 then
(if i.val < 6778 then
(if i.val < 6777 then
[3, 2, 2, 1, 0, 0, 3, 2, 2]
else
[3, 2, 2, 1, 0, 3, 0, 2, 1])
else
(if i.val < 6779 then
[3, 2, 2, 1, 1, 3, 0, 2, 1]
else
[3, 2, 2, 1, 3, 0, 0, 1, 2]))
else
(if i.val < 6782 then
(if i.val < 6781 then
[3, 2, 2, 1, 3, 0, 0, 3, 2]
else
[3, 2, 2, 1, 3, 0, 1, 2, 1])
else
(if i.val < 6783 then
[3, 2, 2, 1, 3, 0, 1, 2, 3]
else
[3, 2, 2, 3, 0, 0, 3, 2, 1])))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row31_cosetWordsPart0053 : Fin 8640 → List (Fin 4) :=
  fun i => (if i.val < 6848 then
(if i.val < 6816 then
(if i.val < 6800 then
(if i.val < 6792 then
(if i.val < 6788 then
(if i.val < 6786 then
(if i.val < 6785 then
[3, 2, 2, 3, 0, 1, 2, 3, 3]
else
[3, 3, 0, 0, 1, 1, 2, 3, 0])
else
(if i.val < 6787 then
[3, 3, 0, 0, 1, 2, 2, 1, 3]
else
[3, 3, 0, 0, 1, 2, 3, 3, 2]))
else
(if i.val < 6790 then
(if i.val < 6789 then
[3, 3, 0, 0, 2, 1, 0, 3, 2]
else
[3, 3, 0, 0, 2, 1, 1, 2, 3])
else
(if i.val < 6791 then
[3, 3, 0, 0, 2, 1, 3, 0, 0]
else
[3, 3, 0, 0, 2, 2, 1, 0, 0])))
else
(if i.val < 6796 then
(if i.val < 6794 then
(if i.val < 6793 then
[3, 3, 0, 0, 2, 2, 1, 3, 3]
else
[3, 3, 0, 0, 2, 3, 3, 2, 1])
else
(if i.val < 6795 then
[3, 3, 0, 1, 1, 0, 2, 2, 1]
else
[3, 3, 0, 1, 1, 0, 3, 2, 1]))
else
(if i.val < 6798 then
(if i.val < 6797 then
[3, 3, 0, 1, 1, 2, 2, 1, 1]
else
[3, 3, 0, 1, 1, 2, 3, 3, 2])
else
(if i.val < 6799 then
[3, 3, 0, 1, 2, 1, 0, 3, 0]
else
[3, 3, 0, 1, 2, 1, 1, 0, 2]))))
else
(if i.val < 6808 then
(if i.val < 6804 then
(if i.val < 6802 then
(if i.val < 6801 then
[3, 3, 0, 1, 2, 1, 1, 3, 3]
else
[3, 3, 0, 1, 2, 1, 3, 0, 0])
else
(if i.val < 6803 then
[3, 3, 0, 1, 2, 1, 3, 0, 1]
else
[3, 3, 0, 1, 2, 1, 3, 3, 0]))
else
(if i.val < 6806 then
(if i.val < 6805 then
[3, 3, 0, 1, 2, 2, 1, 3, 2]
else
[3, 3, 0, 1, 2, 2, 1, 3, 3])
else
(if i.val < 6807 then
[3, 3, 0, 1, 2, 3, 0, 0, 3]
else
[3, 3, 0, 1, 2, 3, 0, 1, 1])))
else
(if i.val < 6812 then
(if i.val < 6810 then
(if i.val < 6809 then
[3, 3, 0, 1, 2, 3, 3, 2, 1]
else
[3, 3, 0, 2, 1, 0, 3, 2, 2])
else
(if i.val < 6811 then
[3, 3, 0, 2, 1, 0, 3, 3, 2]
else
[3, 3, 0, 2, 1, 1, 0, 2, 1]))
else
(if i.val < 6814 then
(if i.val < 6813 then
[3, 3, 0, 2, 1, 1, 0, 2, 3]
else
[3, 3, 0, 2, 1, 1, 0, 3, 2])
else
(if i.val < 6815 then
[3, 3, 0, 2, 1, 1, 2, 3, 2]
else
[3, 3, 0, 2, 1, 1, 3, 2, 2])))))
else
(if i.val < 6832 then
(if i.val < 6824 then
(if i.val < 6820 then
(if i.val < 6818 then
(if i.val < 6817 then
[3, 3, 0, 2, 1, 3, 3, 0, 1]
else
[3, 3, 0, 2, 1, 3, 3, 2, 1])
else
(if i.val < 6819 then
[3, 3, 0, 2, 2, 1, 3, 3, 2]
else
[3, 3, 0, 2, 3, 3, 2, 1, 1]))
else
(if i.val < 6822 then
(if i.val < 6821 then
[3, 3, 2, 1, 0, 3, 2, 2, 1]
else
[3, 3, 2, 1, 0, 3, 2, 2, 3])
else
(if i.val < 6823 then
[3, 3, 2, 1, 0, 3, 3, 0, 1]
else
[3, 3, 2, 1, 1, 0, 0, 2, 3])))
else
(if i.val < 6828 then
(if i.val < 6826 then
(if i.val < 6825 then
[3, 3, 2, 1, 1, 0, 2, 3, 2]
else
[3, 3, 2, 1, 1, 0, 3, 3, 2])
else
(if i.val < 6827 then
[3, 3, 2, 2, 1, 0, 0, 1, 2]
else
[3, 3, 2, 2, 1, 0, 0, 1, 3]))
else
(if i.val < 6830 then
(if i.val < 6829 then
[3, 3, 2, 2, 1, 0, 3, 2, 1]
else
[3, 3, 2, 2, 1, 1, 0, 3, 2])
else
(if i.val < 6831 then
[3, 3, 2, 2, 1, 1, 0, 3, 3]
else
[0, 0, 1, 0, 0, 1, 2, 1, 1, 2]))))
else
(if i.val < 6840 then
(if i.val < 6836 then
(if i.val < 6834 then
(if i.val < 6833 then
[0, 0, 1, 0, 0, 1, 2, 1, 3, 0]
else
[0, 0, 1, 0, 0, 1, 2, 2, 1, 0])
else
(if i.val < 6835 then
[0, 0, 1, 0, 0, 1, 2, 2, 1, 3]
else
[0, 0, 1, 0, 0, 1, 2, 2, 3, 3]))
else
(if i.val < 6838 then
(if i.val < 6837 then
[0, 0, 1, 0, 0, 1, 2, 3, 3, 2]
else
[0, 0, 1, 0, 0, 1, 3, 0, 2, 1])
else
(if i.val < 6839 then
[0, 0, 1, 0, 0, 1, 3, 2, 2, 1]
else
[0, 0, 1, 0, 0, 2, 1, 0, 3, 2])))
else
(if i.val < 6844 then
(if i.val < 6842 then
(if i.val < 6841 then
[0, 0, 1, 0, 0, 2, 1, 1, 2, 3]
else
[0, 0, 1, 0, 0, 2, 1, 3, 0, 1])
else
(if i.val < 6843 then
[0, 0, 1, 0, 0, 2, 2, 1, 0, 0]
else
[0, 0, 1, 0, 0, 2, 2, 1, 1, 3]))
else
(if i.val < 6846 then
(if i.val < 6845 then
[0, 0, 1, 0, 0, 2, 2, 1, 3, 2]
else
[0, 0, 1, 0, 0, 2, 2, 3, 3, 2])
else
(if i.val < 6847 then
[0, 0, 1, 0, 0, 2, 3, 0, 2, 2]
else
[0, 0, 1, 0, 0, 2, 3, 2, 2, 1]))))))
else
(if i.val < 6880 then
(if i.val < 6864 then
(if i.val < 6856 then
(if i.val < 6852 then
(if i.val < 6850 then
(if i.val < 6849 then
[0, 0, 1, 0, 0, 2, 3, 2, 2, 3]
else
[0, 0, 1, 0, 0, 2, 3, 3, 2, 2])
else
(if i.val < 6851 then
[0, 0, 1, 0, 0, 3, 0, 1, 2, 2]
else
[0, 0, 1, 0, 0, 3, 0, 2, 2, 1]))
else
(if i.val < 6854 then
(if i.val < 6853 then
[0, 0, 1, 0, 0, 3, 0, 2, 2, 3]
else
[0, 0, 1, 0, 0, 3, 2, 1, 1, 2])
else
(if i.val < 6855 then
[0, 0, 1, 0, 0, 3, 3, 0, 2, 1]
else
[0, 0, 1, 0, 0, 3, 3, 0, 2, 2])))
else
(if i.val < 6860 then
(if i.val < 6858 then
(if i.val < 6857 then
[0, 0, 1, 0, 0, 3, 3, 2, 2, 1]
else
[0, 0, 1, 0, 2, 1, 0, 0, 1, 2])
else
(if i.val < 6859 then
[0, 0, 1, 0, 2, 1, 0, 3, 3, 2]
else
[0, 0, 1, 0, 2, 1, 1, 0, 3, 2]))
else
(if i.val < 6862 then
(if i.val < 6861 then
[0, 0, 1, 0, 2, 1, 1, 2, 3, 3]
else
[0, 0, 1, 0, 2, 1, 1, 3, 3, 2])
else
(if i.val < 6863 then
[0, 0, 1, 0, 2, 1, 3, 3, 2, 2]
else
[0, 0, 1, 0, 2, 2, 1, 0, 0, 3]))))
else
(if i.val < 6872 then
(if i.val < 6868 then
(if i.val < 6866 then
(if i.val < 6865 then
[0, 0, 1, 0, 2, 2, 1, 0, 3, 2]
else
[0, 0, 1, 0, 2, 2, 1, 0, 3, 3])
else
(if i.val < 6867 then
[0, 0, 1, 0, 2, 2, 1, 3, 0, 0]
else
[0, 0, 1, 0, 2, 2, 1, 3, 0, 2]))
else
(if i.val < 6870 then
(if i.val < 6869 then
[0, 0, 1, 0, 2, 2, 1, 3, 3, 2]
else
[0, 0, 1, 0, 2, 2, 3, 0, 0, 2])
else
(if i.val < 6871 then
[0, 0, 1, 0, 2, 2, 3, 0, 2, 1]
else
[0, 0, 1, 0, 2, 2, 3, 2, 2, 1])))
else
(if i.val < 6876 then
(if i.val < 6874 then
(if i.val < 6873 then
[0, 0, 1, 0, 2, 3, 0, 0, 2, 3]
else
[0, 0, 1, 0, 2, 3, 0, 1, 1, 2])
else
(if i.val < 6875 then
[0, 0, 1, 0, 2, 3, 0, 1, 2, 1]
else
[0, 0, 1, 0, 2, 3, 0, 1, 2, 2]))
else
(if i.val < 6878 then
(if i.val < 6877 then
[0, 0, 1, 0, 2, 3, 0, 1, 2, 3]
else
[0, 0, 1, 0, 2, 3, 2, 1, 1, 0])
else
(if i.val < 6879 then
[0, 0, 1, 0, 2, 3, 3, 0, 1, 2]
else
[0, 0, 1, 0, 2, 3, 3, 0, 2, 1])))))
else
(if i.val < 6896 then
(if i.val < 6888 then
(if i.val < 6884 then
(if i.val < 6882 then
(if i.val < 6881 then
[0, 0, 1, 0, 3, 0, 0, 1, 1, 2]
else
[0, 0, 1, 0, 3, 0, 0, 1, 2, 1])
else
(if i.val < 6883 then
[0, 0, 1, 0, 3, 0, 0, 1, 2, 2]
else
[0, 0, 1, 0, 3, 0, 0, 2, 1, 1]))
else
(if i.val < 6886 then
(if i.val < 6885 then
[0, 0, 1, 0, 3, 0, 0, 2, 3, 2]
else
[0, 0, 1, 0, 3, 0, 0, 2, 3, 3])
else
(if i.val < 6887 then
[0, 0, 1, 0, 3, 0, 1, 1, 2, 1]
else
[0, 0, 1, 0, 3, 0, 1, 1, 2, 2])))
else
(if i.val < 6892 then
(if i.val < 6890 then
(if i.val < 6889 then
[0, 0, 1, 0, 3, 0, 1, 2, 3, 3]
else
[0, 0, 1, 0, 3, 0, 2, 1, 0, 0])
else
(if i.val < 6891 then
[0, 0, 1, 0, 3, 0, 2, 1, 3, 0]
else
[0, 0, 1, 0, 3, 0, 2, 2, 1, 3]))
else
(if i.val < 6894 then
(if i.val < 6893 then
[0, 0, 1, 0, 3, 0, 2, 2, 3, 3]
else
[0, 0, 1, 0, 3, 2, 1, 0, 0, 3])
else
(if i.val < 6895 then
[0, 0, 1, 0, 3, 2, 1, 0, 3, 2]
else
[0, 0, 1, 0, 3, 2, 1, 1, 0, 0]))))
else
(if i.val < 6904 then
(if i.val < 6900 then
(if i.val < 6898 then
(if i.val < 6897 then
[0, 0, 1, 0, 3, 2, 1, 1, 0, 3]
else
[0, 0, 1, 0, 3, 2, 1, 1, 2, 3])
else
(if i.val < 6899 then
[0, 0, 1, 0, 3, 2, 2, 3, 0, 0]
else
[0, 0, 1, 0, 3, 2, 2, 3, 0, 1]))
else
(if i.val < 6902 then
(if i.val < 6901 then
[0, 0, 1, 0, 3, 3, 0, 1, 2, 1]
else
[0, 0, 1, 1, 0, 0, 2, 1, 0, 0])
else
(if i.val < 6903 then
[0, 0, 1, 1, 0, 0, 2, 1, 1, 2]
else
[0, 0, 1, 1, 0, 0, 2, 1, 3, 0])))
else
(if i.val < 6908 then
(if i.val < 6906 then
(if i.val < 6905 then
[0, 0, 1, 1, 0, 0, 2, 2, 1, 3]
else
[0, 0, 1, 1, 0, 0, 2, 2, 3, 3])
else
(if i.val < 6907 then
[0, 0, 1, 1, 0, 0, 2, 3, 0, 0]
else
[0, 0, 1, 1, 0, 0, 2, 3, 0, 1]))
else
(if i.val < 6910 then
(if i.val < 6909 then
[0, 0, 1, 1, 0, 0, 2, 3, 3, 2]
else
[0, 0, 1, 1, 0, 2, 1, 0, 3, 0])
else
(if i.val < 6911 then
[0, 0, 1, 1, 0, 2, 1, 0, 3, 2]
else
[0, 0, 1, 1, 0, 2, 1, 1, 3, 2])))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row31_cosetWordsPart0054 : Fin 8640 → List (Fin 4) :=
  fun i => (if i.val < 6976 then
(if i.val < 6944 then
(if i.val < 6928 then
(if i.val < 6920 then
(if i.val < 6916 then
(if i.val < 6914 then
(if i.val < 6913 then
[0, 0, 1, 1, 0, 2, 2, 1, 0, 0]
else
[0, 0, 1, 1, 0, 2, 2, 3, 0, 0])
else
(if i.val < 6915 then
[0, 0, 1, 1, 0, 2, 2, 3, 0, 1]
else
[0, 0, 1, 1, 0, 2, 3, 0, 0, 2]))
else
(if i.val < 6918 then
(if i.val < 6917 then
[0, 0, 1, 1, 0, 2, 3, 0, 0, 3]
else
[0, 0, 1, 1, 0, 2, 3, 3, 2, 1])
else
(if i.val < 6919 then
[0, 0, 1, 1, 0, 3, 0, 0, 2, 2]
else
[0, 0, 1, 1, 0, 3, 0, 1, 2, 1])))
else
(if i.val < 6924 then
(if i.val < 6922 then
(if i.val < 6921 then
[0, 0, 1, 1, 0, 3, 0, 1, 2, 2]
else
[0, 0, 1, 1, 0, 3, 0, 2, 1, 3])
else
(if i.val < 6923 then
[0, 0, 1, 1, 0, 3, 2, 1, 1, 2]
else
[0, 0, 1, 1, 0, 3, 2, 2, 1, 0]))
else
(if i.val < 6926 then
(if i.val < 6925 then
[0, 0, 1, 1, 0, 3, 3, 0, 1, 2]
else
[0, 0, 1, 1, 2, 1, 0, 0, 1, 2])
else
(if i.val < 6927 then
[0, 0, 1, 1, 2, 1, 0, 3, 0, 0]
else
[0, 0, 1, 1, 2, 1, 0, 3, 0, 1]))))
else
(if i.val < 6936 then
(if i.val < 6932 then
(if i.val < 6930 then
(if i.val < 6929 then
[0, 0, 1, 1, 2, 1, 1, 0, 2, 1]
else
[0, 0, 1, 1, 2, 1, 1, 0, 3, 2])
else
(if i.val < 6931 then
[0, 0, 1, 1, 2, 1, 1, 0, 3, 3]
else
[0, 0, 1, 1, 2, 1, 1, 3, 0, 0]))
else
(if i.val < 6934 then
(if i.val < 6933 then
[0, 0, 1, 1, 2, 1, 1, 3, 0, 1]
else
[0, 0, 1, 1, 2, 1, 1, 3, 2, 2])
else
(if i.val < 6935 then
[0, 0, 1, 1, 2, 1, 1, 3, 3, 2]
else
[0, 0, 1, 1, 2, 1, 3, 3, 0, 0])))
else
(if i.val < 6940 then
(if i.val < 6938 then
(if i.val < 6937 then
[0, 0, 1, 1, 2, 1, 3, 3, 0, 1]
else
[0, 0, 1, 1, 2, 2, 1, 0, 0, 3])
else
(if i.val < 6939 then
[0, 0, 1, 1, 2, 2, 1, 0, 3, 3]
else
[0, 0, 1, 1, 2, 2, 1, 1, 0, 0]))
else
(if i.val < 6942 then
(if i.val < 6941 then
[0, 0, 1, 1, 2, 2, 1, 1, 3, 0]
else
[0, 0, 1, 1, 2, 2, 1, 3, 0, 0])
else
(if i.val < 6943 then
[0, 0, 1, 1, 2, 2, 3, 0, 0, 3]
else
[0, 0, 1, 1, 2, 2, 3, 0, 2, 3])))))
else
(if i.val < 6960 then
(if i.val < 6952 then
(if i.val < 6948 then
(if i.val < 6946 then
(if i.val < 6945 then
[0, 0, 1, 1, 2, 2, 3, 2, 1, 0]
else
[0, 0, 1, 1, 2, 2, 3, 2, 2, 1])
else
(if i.val < 6947 then
[0, 0, 1, 1, 2, 2, 3, 2, 2, 3]
else
[0, 0, 1, 1, 2, 2, 3, 3, 0, 0]))
else
(if i.val < 6950 then
(if i.val < 6949 then
[0, 0, 1, 1, 2, 3, 2, 1, 0, 3]
else
[0, 0, 1, 1, 3, 0, 0, 2, 2, 3])
else
(if i.val < 6951 then
[0, 0, 1, 1, 3, 0, 1, 1, 2, 3]
else
[0, 0, 1, 1, 3, 0, 1, 2, 1, 1])))
else
(if i.val < 6956 then
(if i.val < 6954 then
(if i.val < 6953 then
[0, 0, 1, 1, 3, 0, 1, 2, 2, 1]
else
[0, 0, 1, 1, 3, 0, 1, 2, 3, 3])
else
(if i.val < 6955 then
[0, 0, 1, 1, 3, 0, 2, 2, 1, 1]
else
[0, 0, 1, 1, 3, 0, 2, 3, 3, 2]))
else
(if i.val < 6958 then
(if i.val < 6957 then
[0, 0, 1, 1, 3, 2, 1, 0, 3, 2]
else
[0, 0, 1, 1, 3, 2, 1, 1, 2, 3])
else
(if i.val < 6959 then
[0, 0, 1, 1, 3, 2, 2, 1, 0, 0]
else
[0, 0, 1, 1, 3, 3, 0, 1, 2, 2]))))
else
(if i.val < 6968 then
(if i.val < 6964 then
(if i.val < 6962 then
(if i.val < 6961 then
[0, 0, 1, 1, 3, 3, 0, 2, 2, 1]
else
[0, 0, 1, 2, 1, 0, 0, 1, 2, 3])
else
(if i.val < 6963 then
[0, 0, 1, 2, 1, 0, 3, 2, 1, 1]
else
[0, 0, 1, 2, 1, 1, 0, 0, 2, 3]))
else
(if i.val < 6966 then
(if i.val < 6965 then
[0, 0, 1, 2, 1, 1, 2, 3, 0, 0]
else
[0, 0, 1, 2, 1, 1, 2, 3, 3, 0])
else
(if i.val < 6967 then
[0, 0, 1, 2, 1, 1, 3, 0, 1, 2]
else
[0, 0, 1, 2, 1, 1, 3, 0, 2, 2])))
else
(if i.val < 6972 then
(if i.val < 6970 then
(if i.val < 6969 then
[0, 0, 1, 2, 1, 3, 0, 1, 2, 1]
else
[0, 0, 1, 2, 1, 3, 0, 1, 2, 2])
else
(if i.val < 6971 then
[0, 0, 1, 2, 1, 3, 2, 1, 1, 2]
else
[0, 0, 1, 2, 1, 3, 2, 2, 1, 3]))
else
(if i.val < 6974 then
(if i.val < 6973 then
[0, 0, 1, 2, 1, 3, 2, 2, 3, 0]
else
[0, 0, 1, 2, 1, 3, 3, 0, 1, 2])
else
(if i.val < 6975 then
[0, 0, 1, 2, 1, 3, 3, 0, 2, 2]
else
[0, 0, 1, 2, 1, 3, 3, 2, 1, 1]))))))
else
(if i.val < 7008 then
(if i.val < 6992 then
(if i.val < 6984 then
(if i.val < 6980 then
(if i.val < 6978 then
(if i.val < 6977 then
[0, 0, 1, 2, 1, 3, 3, 2, 2, 1]
else
[0, 0, 1, 2, 2, 1, 0, 3, 0, 1])
else
(if i.val < 6979 then
[0, 0, 1, 2, 2, 1, 0, 3, 0, 2]
else
[0, 0, 1, 2, 2, 1, 0, 3, 2, 1]))
else
(if i.val < 6982 then
(if i.val < 6981 then
[0, 0, 1, 2, 2, 1, 1, 3, 0, 0]
else
[0, 0, 1, 2, 2, 1, 1, 3, 0, 1])
else
(if i.val < 6983 then
[0, 0, 1, 2, 2, 1, 1, 3, 2, 1]
else
[0, 0, 1, 2, 2, 1, 3, 0, 0, 2])))
else
(if i.val < 6988 then
(if i.val < 6986 then
(if i.val < 6985 then
[0, 0, 1, 2, 2, 1, 3, 0, 1, 1]
else
[0, 0, 1, 2, 2, 1, 3, 0, 2, 3])
else
(if i.val < 6987 then
[0, 0, 1, 2, 2, 1, 3, 2, 2, 1]
else
[0, 0, 1, 2, 2, 1, 3, 3, 0, 1]))
else
(if i.val < 6990 then
(if i.val < 6989 then
[0, 0, 1, 2, 2, 1, 3, 3, 0, 2]
else
[0, 0, 1, 2, 2, 3, 0, 0, 3, 2])
else
(if i.val < 6991 then
[0, 0, 1, 2, 2, 3, 0, 2, 2, 1]
else
[0, 0, 1, 2, 2, 3, 2, 2, 1, 3]))))
else
(if i.val < 7000 then
(if i.val < 6996 then
(if i.val < 6994 then
(if i.val < 6993 then
[0, 0, 1, 2, 3, 0, 0, 1, 1, 2]
else
[0, 0, 1, 2, 3, 0, 0, 1, 2, 1])
else
(if i.val < 6995 then
[0, 0, 1, 2, 3, 0, 1, 1, 2, 1]
else
[0, 0, 1, 2, 3, 0, 1, 2, 2, 1]))
else
(if i.val < 6998 then
(if i.val < 6997 then
[0, 0, 1, 2, 3, 0, 1, 2, 2, 3]
else
[0, 0, 1, 2, 3, 0, 1, 2, 3, 0])
else
(if i.val < 6999 then
[0, 0, 1, 2, 3, 0, 2, 1, 1, 2]
else
[0, 0, 1, 2, 3, 0, 2, 2, 3, 0])))
else
(if i.val < 7004 then
(if i.val < 7002 then
(if i.val < 7001 then
[0, 0, 1, 2, 3, 2, 2, 1, 0, 3]
else
[0, 0, 1, 2, 3, 2, 2, 1, 3, 0])
else
(if i.val < 7003 then
[0, 0, 1, 2, 3, 3, 0, 0, 2, 1]
else
[0, 0, 1, 2, 3, 3, 0, 0, 2, 3]))
else
(if i.val < 7006 then
(if i.val < 7005 then
[0, 0, 1, 2, 3, 3, 0, 1, 1, 2]
else
[0, 0, 1, 2, 3, 3, 0, 1, 2, 1])
else
(if i.val < 7007 then
[0, 0, 1, 2, 3, 3, 0, 1, 2, 2]
else
[0, 0, 1, 2, 3, 3, 2, 1, 0, 0])))))
else
(if i.val < 7024 then
(if i.val < 7016 then
(if i.val < 7012 then
(if i.val < 7010 then
(if i.val < 7009 then
[0, 0, 1, 2, 3, 3, 2, 1, 0, 3]
else
[0, 0, 1, 3, 0, 0, 1, 1, 2, 2])
else
(if i.val < 7011 then
[0, 0, 1, 3, 0, 0, 1, 1, 2, 3]
else
[0, 0, 1, 3, 0, 0, 1, 2, 1, 1]))
else
(if i.val < 7014 then
(if i.val < 7013 then
[0, 0, 1, 3, 0, 0, 2, 1, 1, 2]
else
[0, 0, 1, 3, 0, 1, 1, 2, 2, 1])
else
(if i.val < 7015 then
[0, 0, 1, 3, 0, 1, 1, 2, 2, 3]
else
[0, 0, 1, 3, 0, 1, 2, 1, 0, 0])))
else
(if i.val < 7020 then
(if i.val < 7018 then
(if i.val < 7017 then
[0, 0, 1, 3, 0, 1, 2, 1, 3, 0]
else
[0, 0, 1, 3, 0, 1, 2, 2, 1, 0])
else
(if i.val < 7019 then
[0, 0, 1, 3, 0, 1, 2, 2, 1, 1]
else
[0, 0, 1, 3, 0, 1, 2, 2, 1, 3]))
else
(if i.val < 7022 then
(if i.val < 7021 then
[0, 0, 1, 3, 0, 1, 2, 3, 3, 0]
else
[0, 0, 1, 3, 0, 2, 1, 1, 3, 2])
else
(if i.val < 7023 then
[0, 0, 1, 3, 0, 2, 3, 3, 0, 2]
else
[0, 0, 1, 3, 2, 1, 1, 0, 0, 2]))))
else
(if i.val < 7032 then
(if i.val < 7028 then
(if i.val < 7026 then
(if i.val < 7025 then
[0, 0, 1, 3, 2, 1, 1, 2, 3, 3]
else
[0, 0, 1, 3, 2, 2, 1, 0, 3, 2])
else
(if i.val < 7027 then
[0, 0, 1, 3, 2, 2, 1, 1, 3, 2]
else
[0, 0, 1, 3, 3, 0, 1, 2, 1, 3]))
else
(if i.val < 7030 then
(if i.val < 7029 then
[0, 0, 1, 3, 3, 0, 2, 1, 1, 2]
else
[0, 0, 1, 3, 3, 0, 2, 2, 1, 1])
else
(if i.val < 7031 then
[0, 0, 1, 3, 3, 0, 2, 2, 1, 3]
else
[0, 0, 1, 3, 3, 2, 1, 0, 3, 3])))
else
(if i.val < 7036 then
(if i.val < 7034 then
(if i.val < 7033 then
[0, 0, 1, 3, 3, 2, 1, 1, 2, 3]
else
[0, 0, 2, 1, 0, 0, 1, 2, 2, 3])
else
(if i.val < 7035 then
[0, 0, 2, 1, 0, 0, 1, 2, 3, 3]
else
[0, 0, 2, 1, 0, 0, 1, 3, 0, 2]))
else
(if i.val < 7038 then
(if i.val < 7037 then
[0, 0, 2, 1, 0, 3, 0, 0, 1, 2]
else
[0, 0, 2, 1, 0, 3, 0, 0, 2, 1])
else
(if i.val < 7039 then
[0, 0, 2, 1, 0, 3, 0, 2, 1, 0]
else
[0, 0, 2, 1, 0, 3, 0, 2, 1, 1])))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row31_cosetWordsPart0055 : Fin 8640 → List (Fin 4) :=
  fun i => (if i.val < 7104 then
(if i.val < 7072 then
(if i.val < 7056 then
(if i.val < 7048 then
(if i.val < 7044 then
(if i.val < 7042 then
(if i.val < 7041 then
[0, 0, 2, 1, 0, 3, 0, 2, 1, 3]
else
[0, 0, 2, 1, 0, 3, 0, 2, 2, 1])
else
(if i.val < 7043 then
[0, 0, 2, 1, 0, 3, 0, 2, 2, 3]
else
[0, 0, 2, 1, 0, 3, 2, 1, 1, 0]))
else
(if i.val < 7046 then
(if i.val < 7045 then
[0, 0, 2, 1, 0, 3, 2, 2, 1, 0]
else
[0, 0, 2, 1, 0, 3, 3, 0, 1, 2])
else
(if i.val < 7047 then
[0, 0, 2, 1, 1, 0, 0, 2, 1, 3]
else
[0, 0, 2, 1, 1, 0, 0, 2, 3, 0])))
else
(if i.val < 7052 then
(if i.val < 7050 then
(if i.val < 7049 then
[0, 0, 2, 1, 1, 0, 0, 2, 3, 3]
else
[0, 0, 2, 1, 1, 0, 2, 1, 1, 2])
else
(if i.val < 7051 then
[0, 0, 2, 1, 1, 0, 2, 1, 3, 0]
else
[0, 0, 2, 1, 1, 0, 2, 3, 2, 1]))
else
(if i.val < 7054 then
(if i.val < 7053 then
[0, 0, 2, 1, 1, 0, 3, 0, 2, 1]
else
[0, 0, 2, 1, 1, 0, 3, 0, 2, 2])
else
(if i.val < 7055 then
[0, 0, 2, 1, 1, 0, 3, 0, 2, 3]
else
[0, 0, 2, 1, 1, 0, 3, 2, 1, 0]))))
else
(if i.val < 7064 then
(if i.val < 7060 then
(if i.val < 7058 then
(if i.val < 7057 then
[0, 0, 2, 1, 1, 2, 3, 0, 0, 3]
else
[0, 0, 2, 1, 1, 2, 3, 2, 1, 0])
else
(if i.val < 7059 then
[0, 0, 2, 1, 1, 3, 0, 1, 2, 1]
else
[0, 0, 2, 1, 1, 3, 0, 1, 2, 2]))
else
(if i.val < 7062 then
(if i.val < 7061 then
[0, 0, 2, 1, 1, 3, 2, 2, 1, 0]
else
[0, 0, 2, 1, 1, 3, 2, 2, 3, 0])
else
(if i.val < 7063 then
[0, 0, 2, 1, 1, 3, 3, 0, 1, 2]
else
[0, 0, 2, 1, 3, 0, 0, 1, 2, 2])))
else
(if i.val < 7068 then
(if i.val < 7066 then
(if i.val < 7065 then
[0, 0, 2, 1, 3, 0, 1, 2, 1, 0]
else
[0, 0, 2, 1, 3, 0, 1, 2, 1, 1])
else
(if i.val < 7067 then
[0, 0, 2, 1, 3, 0, 1, 2, 2, 3]
else
[0, 0, 2, 1, 3, 0, 1, 2, 3, 3]))
else
(if i.val < 7070 then
(if i.val < 7069 then
[0, 0, 2, 1, 3, 2, 1, 0, 3, 2]
else
[0, 0, 2, 1, 3, 2, 1, 1, 2, 3])
else
(if i.val < 7071 then
[0, 0, 2, 1, 3, 3, 0, 0, 2, 3]
else
[0, 0, 2, 1, 3, 3, 0, 1, 2, 3])))))
else
(if i.val < 7088 then
(if i.val < 7080 then
(if i.val < 7076 then
(if i.val < 7074 then
(if i.val < 7073 then
[0, 0, 2, 1, 3, 3, 0, 2, 1, 1]
else
[0, 0, 2, 1, 3, 3, 0, 2, 2, 1])
else
(if i.val < 7075 then
[0, 0, 2, 1, 3, 3, 2, 1, 1, 0]
else
[0, 0, 2, 2, 1, 0, 0, 1, 2, 3]))
else
(if i.val < 7078 then
(if i.val < 7077 then
[0, 0, 2, 2, 1, 0, 0, 1, 3, 2]
else
[0, 0, 2, 2, 1, 0, 0, 3, 3, 2])
else
(if i.val < 7079 then
[0, 0, 2, 2, 1, 0, 3, 0, 2, 1]
else
[0, 0, 2, 2, 1, 0, 3, 0, 2, 3])))
else
(if i.val < 7084 then
(if i.val < 7082 then
(if i.val < 7081 then
[0, 0, 2, 2, 1, 0, 3, 2, 1, 0]
else
[0, 0, 2, 2, 1, 1, 0, 3, 0, 2])
else
(if i.val < 7083 then
[0, 0, 2, 2, 1, 1, 0, 3, 2, 1]
else
[0, 0, 2, 2, 1, 1, 3, 2, 1, 0]))
else
(if i.val < 7086 then
(if i.val < 7085 then
[0, 0, 2, 2, 1, 3, 0, 0, 3, 2]
else
[0, 0, 2, 2, 1, 3, 0, 1, 2, 1])
else
(if i.val < 7087 then
[0, 0, 2, 2, 1, 3, 0, 1, 2, 3]
else
[0, 0, 2, 2, 1, 3, 2, 1, 1, 0]))))
else
(if i.val < 7096 then
(if i.val < 7092 then
(if i.val < 7090 then
(if i.val < 7089 then
[0, 0, 2, 2, 1, 3, 3, 0, 1, 2]
else
[0, 0, 2, 2, 1, 3, 3, 2, 1, 0])
else
(if i.val < 7091 then
[0, 0, 2, 2, 3, 0, 0, 2, 2, 3]
else
[0, 0, 2, 2, 3, 0, 0, 3, 2, 1]))
else
(if i.val < 7094 then
(if i.val < 7093 then
[0, 0, 2, 2, 3, 0, 1, 2, 1, 0]
else
[0, 0, 2, 2, 3, 0, 1, 2, 3, 0])
else
(if i.val < 7095 then
[0, 0, 2, 2, 3, 0, 1, 2, 3, 3]
else
[0, 0, 2, 2, 3, 0, 2, 2, 1, 3])))
else
(if i.val < 7100 then
(if i.val < 7098 then
(if i.val < 7097 then
[0, 0, 2, 2, 3, 2, 2, 1, 0, 0]
else
[0, 0, 2, 2, 3, 2, 2, 1, 1, 3])
else
(if i.val < 7099 then
[0, 0, 2, 2, 3, 3, 0, 1, 2, 1]
else
[0, 0, 2, 2, 3, 3, 0, 1, 2, 3]))
else
(if i.val < 7102 then
(if i.val < 7101 then
[0, 0, 2, 2, 3, 3, 0, 2, 1, 0]
else
[0, 0, 2, 2, 3, 3, 0, 2, 1, 1])
else
(if i.val < 7103 then
[0, 0, 2, 3, 0, 0, 1, 1, 2, 3]
else
[0, 0, 2, 3, 0, 0, 2, 1, 1, 2]))))))
else
(if i.val < 7136 then
(if i.val < 7120 then
(if i.val < 7112 then
(if i.val < 7108 then
(if i.val < 7106 then
(if i.val < 7105 then
[0, 0, 2, 3, 0, 0, 2, 3, 2, 1]
else
[0, 0, 2, 3, 0, 0, 2, 3, 3, 2])
else
(if i.val < 7107 then
[0, 0, 2, 3, 0, 0, 3, 2, 1, 0]
else
[0, 0, 2, 3, 0, 1, 1, 0, 3, 2]))
else
(if i.val < 7110 then
(if i.val < 7109 then
[0, 0, 2, 3, 0, 1, 2, 1, 1, 0]
else
[0, 0, 2, 3, 0, 1, 2, 2, 3, 0])
else
(if i.val < 7111 then
[0, 0, 2, 3, 0, 1, 2, 2, 3, 3]
else
[0, 0, 2, 3, 0, 1, 2, 3, 0, 1])))
else
(if i.val < 7116 then
(if i.val < 7114 then
(if i.val < 7113 then
[0, 0, 2, 3, 0, 1, 2, 3, 3, 0]
else
[0, 0, 2, 3, 0, 2, 2, 1, 0, 0])
else
(if i.val < 7115 then
[0, 0, 2, 3, 0, 2, 2, 1, 0, 3]
else
[0, 0, 2, 3, 0, 2, 2, 3, 3, 0]))
else
(if i.val < 7118 then
(if i.val < 7117 then
[0, 0, 2, 3, 2, 1, 0, 3, 2, 2]
else
[0, 0, 2, 3, 2, 2, 1, 0, 3, 0])
else
(if i.val < 7119 then
[0, 0, 2, 3, 2, 2, 1, 1, 0, 0]
else
[0, 0, 2, 3, 2, 2, 1, 3, 0, 1]))))
else
(if i.val < 7128 then
(if i.val < 7124 then
(if i.val < 7122 then
(if i.val < 7121 then
[0, 0, 2, 3, 2, 2, 3, 0, 1, 2]
else
[0, 0, 2, 3, 3, 0, 0, 2, 1, 3])
else
(if i.val < 7123 then
[0, 0, 2, 3, 3, 0, 1, 2, 1, 3]
else
[0, 0, 2, 3, 3, 0, 2, 1, 0, 0]))
else
(if i.val < 7126 then
(if i.val < 7125 then
[0, 0, 2, 3, 3, 0, 2, 2, 1, 3]
else
[0, 0, 2, 3, 3, 0, 2, 2, 3, 3])
else
(if i.val < 7127 then
[0, 0, 2, 3, 3, 2, 1, 0, 0, 3]
else
[0, 0, 2, 3, 3, 2, 2, 1, 0, 3])))
else
(if i.val < 7132 then
(if i.val < 7130 then
(if i.val < 7129 then
[0, 0, 2, 3, 3, 2, 2, 1, 1, 0]
else
[0, 0, 3, 0, 0, 1, 1, 2, 1, 3])
else
(if i.val < 7131 then
[0, 0, 3, 0, 0, 1, 1, 2, 2, 1]
else
[0, 0, 3, 0, 0, 1, 1, 2, 3, 0]))
else
(if i.val < 7134 then
(if i.val < 7133 then
[0, 0, 3, 0, 0, 1, 1, 2, 3, 2]
else
[0, 0, 3, 0, 0, 1, 1, 2, 3, 3])
else
(if i.val < 7135 then
[0, 0, 3, 0, 0, 1, 2, 2, 1, 1]
else
[0, 0, 3, 0, 0, 1, 2, 2, 3, 3])))))
else
(if i.val < 7152 then
(if i.val < 7144 then
(if i.val < 7140 then
(if i.val < 7138 then
(if i.val < 7137 then
[0, 0, 3, 0, 0, 1, 2, 3, 3, 2]
else
[0, 0, 3, 0, 0, 1, 3, 2, 2, 1])
else
(if i.val < 7139 then
[0, 0, 3, 0, 0, 2, 1, 1, 2, 3]
else
[0, 0, 3, 0, 0, 2, 1, 1, 3, 2]))
else
(if i.val < 7142 then
(if i.val < 7141 then
[0, 0, 3, 0, 0, 2, 2, 1, 0, 0]
else
[0, 0, 3, 0, 0, 2, 2, 1, 3, 2])
else
(if i.val < 7143 then
[0, 0, 3, 0, 0, 2, 2, 3, 0, 1]
else
[0, 0, 3, 0, 0, 2, 2, 3, 2, 2])))
else
(if i.val < 7148 then
(if i.val < 7146 then
(if i.val < 7145 then
[0, 0, 3, 0, 0, 2, 3, 2, 1, 0]
else
[0, 0, 3, 0, 0, 2, 3, 3, 2, 1])
else
(if i.val < 7147 then
[0, 0, 3, 0, 0, 3, 2, 1, 0, 0]
else
[0, 0, 3, 0, 0, 3, 2, 1, 1, 2]))
else
(if i.val < 7150 then
(if i.val < 7149 then
[0, 0, 3, 0, 0, 3, 2, 2, 1, 0]
else
[0, 0, 3, 0, 1, 1, 0, 3, 2, 1])
else
(if i.val < 7151 then
[0, 0, 3, 0, 1, 2, 1, 0, 0, 3]
else
[0, 0, 3, 0, 1, 2, 1, 1, 0, 0]))))
else
(if i.val < 7160 then
(if i.val < 7156 then
(if i.val < 7154 then
(if i.val < 7153 then
[0, 0, 3, 0, 1, 2, 1, 1, 0, 3]
else
[0, 0, 3, 0, 1, 2, 1, 3, 2, 2])
else
(if i.val < 7155 then
[0, 0, 3, 0, 1, 2, 2, 1, 3, 3]
else
[0, 0, 3, 0, 1, 2, 2, 3, 0, 0]))
else
(if i.val < 7158 then
(if i.val < 7157 then
[0, 0, 3, 0, 1, 2, 2, 3, 3, 0]
else
[0, 0, 3, 0, 1, 2, 3, 0, 0, 3])
else
(if i.val < 7159 then
[0, 0, 3, 0, 1, 2, 3, 0, 1, 1]
else
[0, 0, 3, 0, 1, 2, 3, 3, 0, 1])))
else
(if i.val < 7164 then
(if i.val < 7162 then
(if i.val < 7161 then
[0, 0, 3, 0, 1, 2, 3, 3, 2, 1]
else
[0, 0, 3, 0, 2, 1, 0, 3, 2, 2])
else
(if i.val < 7163 then
[0, 0, 3, 0, 2, 1, 1, 0, 2, 1]
else
[0, 0, 3, 0, 2, 1, 1, 0, 3, 2]))
else
(if i.val < 7166 then
(if i.val < 7165 then
[0, 0, 3, 0, 2, 1, 1, 2, 3, 2]
else
[0, 0, 3, 0, 2, 1, 1, 3, 2, 2])
else
(if i.val < 7167 then
[0, 0, 3, 0, 2, 1, 1, 3, 3, 2]
else
[0, 0, 3, 0, 2, 2, 1, 0, 0, 3])))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row31_cosetWordsPart0056 : Fin 8640 → List (Fin 4) :=
  fun i => (if i.val < 7232 then
(if i.val < 7200 then
(if i.val < 7184 then
(if i.val < 7176 then
(if i.val < 7172 then
(if i.val < 7170 then
(if i.val < 7169 then
[0, 0, 3, 0, 2, 2, 1, 0, 3, 3]
else
[0, 0, 3, 0, 2, 2, 1, 3, 0, 0])
else
(if i.val < 7171 then
[0, 0, 3, 0, 2, 2, 1, 3, 0, 2]
else
[0, 0, 3, 0, 2, 2, 3, 0, 1, 2]))
else
(if i.val < 7174 then
(if i.val < 7173 then
[0, 0, 3, 0, 2, 3, 3, 0, 2, 1]
else
[0, 0, 3, 2, 1, 0, 0, 1, 2, 2])
else
(if i.val < 7175 then
[0, 0, 3, 2, 1, 0, 0, 3, 3, 2]
else
[0, 0, 3, 2, 1, 0, 3, 2, 2, 1])))
else
(if i.val < 7180 then
(if i.val < 7178 then
(if i.val < 7177 then
[0, 0, 3, 2, 1, 0, 3, 2, 2, 3]
else
[0, 0, 3, 2, 1, 1, 0, 3, 2, 1])
else
(if i.val < 7179 then
[0, 0, 3, 2, 1, 1, 0, 3, 3, 2]
else
[0, 0, 3, 2, 1, 1, 2, 3, 0, 1]))
else
(if i.val < 7182 then
(if i.val < 7181 then
[0, 0, 3, 2, 2, 1, 0, 3, 0, 1]
else
[0, 0, 3, 2, 2, 1, 1, 3, 0, 0])
else
(if i.val < 7183 then
[0, 0, 3, 2, 2, 1, 1, 3, 0, 1]
else
[0, 0, 3, 2, 2, 1, 3, 0, 1, 1]))))
else
(if i.val < 7192 then
(if i.val < 7188 then
(if i.val < 7186 then
(if i.val < 7185 then
[0, 0, 3, 2, 2, 1, 3, 0, 1, 2]
else
[0, 0, 3, 2, 2, 1, 3, 0, 2, 3])
else
(if i.val < 7187 then
[0, 0, 3, 2, 2, 1, 3, 2, 2, 1]
else
[0, 0, 3, 2, 2, 3, 0, 1, 2, 3]))
else
(if i.val < 7190 then
(if i.val < 7189 then
[0, 0, 3, 3, 0, 0, 2, 1, 0, 0]
else
[0, 0, 3, 3, 0, 1, 2, 1, 1, 0])
else
(if i.val < 7191 then
[0, 0, 3, 3, 0, 1, 2, 2, 1, 3]
else
[0, 0, 3, 3, 0, 1, 2, 3, 0, 0])))
else
(if i.val < 7196 then
(if i.val < 7194 then
(if i.val < 7193 then
[0, 0, 3, 3, 0, 2, 1, 0, 3, 0]
else
[0, 0, 3, 3, 0, 2, 1, 0, 3, 3])
else
(if i.val < 7195 then
[0, 0, 3, 3, 0, 2, 3, 3, 0, 2]
else
[0, 0, 3, 3, 0, 2, 3, 3, 2, 1]))
else
(if i.val < 7198 then
(if i.val < 7197 then
[0, 0, 3, 3, 2, 1, 0, 3, 2, 2]
else
[0, 0, 3, 3, 2, 1, 1, 0, 3, 3])
else
(if i.val < 7199 then
[0, 0, 3, 3, 2, 2, 1, 0, 3, 3]
else
[0, 0, 3, 3, 2, 2, 1, 1, 0, 0])))))
else
(if i.val < 7216 then
(if i.val < 7208 then
(if i.val < 7204 then
(if i.val < 7202 then
(if i.val < 7201 then
[0, 1, 0, 0, 1, 2, 1, 0, 0, 3]
else
[0, 1, 0, 0, 1, 2, 1, 3, 0, 0])
else
(if i.val < 7203 then
[0, 1, 0, 0, 1, 2, 2, 1, 1, 0]
else
[0, 1, 0, 0, 1, 2, 2, 1, 3, 0]))
else
(if i.val < 7206 then
(if i.val < 7205 then
[0, 1, 0, 0, 1, 2, 2, 1, 3, 2]
else
[0, 1, 0, 0, 1, 2, 2, 3, 0, 1])
else
(if i.val < 7207 then
[0, 1, 0, 0, 1, 2, 2, 3, 2, 1]
else
[0, 1, 0, 0, 1, 2, 3, 0, 0, 2])))
else
(if i.val < 7212 then
(if i.val < 7210 then
(if i.val < 7209 then
[0, 1, 0, 0, 1, 2, 3, 0, 0, 3]
else
[0, 1, 0, 0, 1, 3, 0, 0, 2, 2])
else
(if i.val < 7211 then
[0, 1, 0, 0, 1, 3, 0, 2, 1, 1]
else
[0, 1, 0, 0, 2, 1, 1, 0, 2, 1]))
else
(if i.val < 7214 then
(if i.val < 7213 then
[0, 1, 0, 0, 2, 1, 1, 2, 3, 0]
else
[0, 1, 0, 0, 2, 1, 1, 3, 3, 2])
else
(if i.val < 7215 then
[0, 1, 0, 0, 2, 1, 3, 0, 1, 1]
else
[0, 1, 0, 0, 2, 1, 3, 2, 2, 3]))))
else
(if i.val < 7224 then
(if i.val < 7220 then
(if i.val < 7218 then
(if i.val < 7217 then
[0, 1, 0, 0, 2, 1, 3, 3, 2, 2]
else
[0, 1, 0, 0, 2, 2, 1, 0, 3, 0])
else
(if i.val < 7219 then
[0, 1, 0, 0, 2, 2, 1, 0, 3, 2]
else
[0, 1, 0, 0, 2, 2, 1, 1, 0, 3]))
else
(if i.val < 7222 then
(if i.val < 7221 then
[0, 1, 0, 0, 2, 2, 1, 1, 3, 2]
else
[0, 1, 0, 0, 2, 2, 1, 3, 0, 0])
else
(if i.val < 7223 then
[0, 1, 0, 0, 2, 2, 1, 3, 0, 1]
else
[0, 1, 0, 0, 2, 2, 3, 0, 0, 3])))
else
(if i.val < 7228 then
(if i.val < 7226 then
(if i.val < 7225 then
[0, 1, 0, 0, 2, 2, 3, 3, 2, 2]
else
[0, 1, 0, 0, 2, 3, 0, 1, 2, 2])
else
(if i.val < 7227 then
[0, 1, 0, 0, 2, 3, 2, 2, 1, 3]
else
[0, 1, 0, 0, 2, 3, 2, 2, 3, 0]))
else
(if i.val < 7230 then
(if i.val < 7229 then
[0, 1, 0, 0, 2, 3, 3, 2, 2, 1]
else
[0, 1, 0, 0, 3, 0, 0, 1, 1, 2])
else
(if i.val < 7231 then
[0, 1, 0, 0, 3, 0, 0, 3, 2, 2]
else
[0, 1, 0, 0, 3, 0, 1, 2, 2, 1]))))))
else
(if i.val < 7264 then
(if i.val < 7248 then
(if i.val < 7240 then
(if i.val < 7236 then
(if i.val < 7234 then
(if i.val < 7233 then
[0, 1, 0, 0, 3, 0, 1, 2, 2, 3]
else
[0, 1, 0, 0, 3, 2, 1, 1, 2, 3])
else
(if i.val < 7235 then
[0, 1, 0, 0, 3, 3, 0, 0, 2, 1]
else
[0, 1, 0, 0, 3, 3, 0, 0, 2, 2]))
else
(if i.val < 7238 then
(if i.val < 7237 then
[0, 1, 0, 0, 3, 3, 0, 1, 2, 3]
else
[0, 1, 0, 0, 3, 3, 0, 2, 1, 1])
else
(if i.val < 7239 then
[0, 1, 0, 0, 3, 3, 0, 2, 3, 3]
else
[0, 1, 0, 0, 3, 3, 2, 1, 0, 0])))
else
(if i.val < 7244 then
(if i.val < 7242 then
(if i.val < 7241 then
[0, 1, 0, 0, 3, 3, 2, 1, 0, 3]
else
[0, 1, 0, 0, 3, 3, 2, 1, 1, 0])
else
(if i.val < 7243 then
[0, 1, 0, 0, 3, 3, 2, 2, 1, 1]
else
[0, 1, 0, 2, 1, 0, 3, 2, 2, 1]))
else
(if i.val < 7246 then
(if i.val < 7245 then
[0, 1, 0, 2, 1, 0, 3, 2, 2, 3]
else
[0, 1, 0, 2, 1, 0, 3, 3, 0, 1])
else
(if i.val < 7247 then
[0, 1, 0, 2, 1, 0, 3, 3, 2, 1]
else
[0, 1, 0, 2, 1, 1, 0, 0, 2, 3]))))
else
(if i.val < 7256 then
(if i.val < 7252 then
(if i.val < 7250 then
(if i.val < 7249 then
[0, 1, 0, 2, 1, 1, 2, 3, 0, 0]
else
[0, 1, 0, 2, 1, 1, 2, 3, 3, 0])
else
(if i.val < 7251 then
[0, 1, 0, 2, 1, 1, 3, 0, 2, 2]
else
[0, 1, 0, 2, 1, 3, 2, 2, 3, 0]))
else
(if i.val < 7254 then
(if i.val < 7253 then
[0, 1, 0, 2, 1, 3, 3, 0, 1, 2]
else
[0, 1, 0, 2, 1, 3, 3, 2, 2, 1])
else
(if i.val < 7255 then
[0, 1, 0, 2, 2, 1, 0, 0, 1, 3]
else
[0, 1, 0, 2, 2, 1, 0, 3, 0, 0])))
else
(if i.val < 7260 then
(if i.val < 7258 then
(if i.val < 7257 then
[0, 1, 0, 2, 2, 1, 0, 3, 0, 1]
else
[0, 1, 0, 2, 2, 1, 0, 3, 2, 1])
else
(if i.val < 7259 then
[0, 1, 0, 2, 2, 1, 1, 0, 3, 2]
else
[0, 1, 0, 2, 2, 1, 1, 3, 0, 1]))
else
(if i.val < 7262 then
(if i.val < 7261 then
[0, 1, 0, 2, 2, 1, 1, 3, 2, 1]
else
[0, 1, 0, 2, 2, 1, 3, 0, 0, 2])
else
(if i.val < 7263 then
[0, 1, 0, 2, 2, 1, 3, 0, 1, 2]
else
[0, 1, 0, 2, 2, 1, 3, 2, 1, 1])))))
else
(if i.val < 7280 then
(if i.val < 7272 then
(if i.val < 7268 then
(if i.val < 7266 then
(if i.val < 7265 then
[0, 1, 0, 2, 2, 1, 3, 3, 0, 2]
else
[0, 1, 0, 2, 2, 3, 0, 2, 2, 1])
else
(if i.val < 7267 then
[0, 1, 0, 2, 2, 3, 2, 2, 1, 3]
else
[0, 1, 0, 2, 2, 3, 3, 0, 2, 2]))
else
(if i.val < 7270 then
(if i.val < 7269 then
[0, 1, 0, 2, 3, 0, 1, 1, 2, 3]
else
[0, 1, 0, 2, 3, 0, 1, 2, 2, 1])
else
(if i.val < 7271 then
[0, 1, 0, 2, 3, 0, 2, 1, 3, 2]
else
[0, 1, 0, 2, 3, 3, 0, 0, 2, 3])))
else
(if i.val < 7276 then
(if i.val < 7274 then
(if i.val < 7273 then
[0, 1, 0, 2, 3, 3, 0, 1, 1, 2]
else
[0, 1, 0, 2, 3, 3, 0, 1, 2, 1])
else
(if i.val < 7275 then
[0, 1, 0, 2, 3, 3, 0, 1, 2, 3]
else
[0, 1, 0, 2, 3, 3, 0, 2, 2, 1]))
else
(if i.val < 7278 then
(if i.val < 7277 then
[0, 1, 0, 2, 3, 3, 0, 2, 3, 3]
else
[0, 1, 0, 2, 3, 3, 2, 1, 0, 3])
else
(if i.val < 7279 then
[0, 1, 0, 3, 0, 0, 1, 1, 2, 1]
else
[0, 1, 0, 3, 0, 0, 1, 1, 2, 2]))))
else
(if i.val < 7288 then
(if i.val < 7284 then
(if i.val < 7282 then
(if i.val < 7281 then
[0, 1, 0, 3, 0, 0, 1, 2, 1, 1]
else
[0, 1, 0, 3, 0, 0, 1, 2, 3, 2])
else
(if i.val < 7283 then
[0, 1, 0, 3, 0, 0, 1, 2, 3, 3]
else
[0, 1, 0, 3, 0, 0, 2, 1, 1, 2]))
else
(if i.val < 7286 then
(if i.val < 7285 then
[0, 1, 0, 3, 0, 0, 3, 2, 2, 1]
else
[0, 1, 0, 3, 0, 1, 1, 2, 2, 1])
else
(if i.val < 7287 then
[0, 1, 0, 3, 0, 1, 1, 2, 2, 3]
else
[0, 1, 0, 3, 2, 1, 0, 0, 1, 2])))
else
(if i.val < 7292 then
(if i.val < 7290 then
(if i.val < 7289 then
[0, 1, 0, 3, 2, 1, 1, 0, 0, 2]
else
[0, 1, 0, 3, 2, 1, 1, 0, 2, 3])
else
(if i.val < 7291 then
[0, 1, 0, 3, 2, 2, 1, 0, 3, 2]
else
[0, 1, 0, 3, 2, 2, 3, 0, 0, 3]))
else
(if i.val < 7294 then
(if i.val < 7293 then
[0, 1, 0, 3, 2, 2, 3, 0, 1, 2]
else
[0, 1, 0, 3, 3, 0, 0, 2, 2, 1])
else
(if i.val < 7295 then
[0, 1, 0, 3, 3, 0, 0, 2, 3, 3]
else
[0, 1, 0, 3, 3, 0, 1, 2, 1, 0])))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row31_cosetWordsPart0057 : Fin 8640 → List (Fin 4) :=
  fun i => (if i.val < 7360 then
(if i.val < 7328 then
(if i.val < 7312 then
(if i.val < 7304 then
(if i.val < 7300 then
(if i.val < 7298 then
(if i.val < 7297 then
[0, 1, 0, 3, 3, 0, 1, 2, 1, 3]
else
[0, 1, 0, 3, 3, 0, 1, 2, 2, 1])
else
(if i.val < 7299 then
[0, 1, 0, 3, 3, 0, 1, 2, 2, 3]
else
[0, 1, 0, 3, 3, 0, 2, 1, 0, 0]))
else
(if i.val < 7302 then
(if i.val < 7301 then
[0, 1, 0, 3, 3, 0, 2, 2, 1, 0]
else
[0, 1, 0, 3, 3, 0, 2, 3, 3, 2])
else
(if i.val < 7303 then
[0, 1, 1, 0, 0, 2, 1, 0, 3, 0]
else
[0, 1, 1, 0, 0, 2, 1, 0, 3, 2])))
else
(if i.val < 7308 then
(if i.val < 7306 then
(if i.val < 7305 then
[0, 1, 1, 0, 0, 2, 1, 1, 2, 3]
else
[0, 1, 1, 0, 0, 2, 1, 3, 0, 0])
else
(if i.val < 7307 then
[0, 1, 1, 0, 0, 2, 2, 1, 3, 0]
else
[0, 1, 1, 0, 0, 2, 2, 3, 0, 1]))
else
(if i.val < 7310 then
(if i.val < 7309 then
[0, 1, 1, 0, 0, 2, 3, 0, 0, 3]
else
[0, 1, 1, 0, 0, 2, 3, 0, 1, 1])
else
(if i.val < 7311 then
[0, 1, 1, 0, 0, 2, 3, 0, 2, 2]
else
[0, 1, 1, 0, 0, 2, 3, 3, 0, 2]))))
else
(if i.val < 7320 then
(if i.val < 7316 then
(if i.val < 7314 then
(if i.val < 7313 then
[0, 1, 1, 0, 0, 2, 3, 3, 2, 1]
else
[0, 1, 1, 0, 0, 3, 0, 1, 2, 1])
else
(if i.val < 7315 then
[0, 1, 1, 0, 0, 3, 0, 1, 2, 2]
else
[0, 1, 1, 0, 0, 3, 3, 0, 2, 2]))
else
(if i.val < 7318 then
(if i.val < 7317 then
[0, 1, 1, 0, 0, 3, 3, 0, 2, 3]
else
[0, 1, 1, 0, 2, 1, 0, 3, 3, 2])
else
(if i.val < 7319 then
[0, 1, 1, 0, 2, 1, 1, 0, 2, 1]
else
[0, 1, 1, 0, 2, 1, 1, 0, 2, 3])))
else
(if i.val < 7324 then
(if i.val < 7322 then
(if i.val < 7321 then
[0, 1, 1, 0, 2, 1, 1, 0, 3, 2]
else
[0, 1, 1, 0, 2, 1, 1, 2, 3, 0])
else
(if i.val < 7323 then
[0, 1, 1, 0, 2, 1, 1, 2, 3, 3]
else
[0, 1, 1, 0, 2, 1, 1, 3, 0, 1]))
else
(if i.val < 7326 then
(if i.val < 7325 then
[0, 1, 1, 0, 2, 1, 1, 3, 0, 2]
else
[0, 1, 1, 0, 2, 1, 1, 3, 2, 1])
else
(if i.val < 7327 then
[0, 1, 1, 0, 2, 1, 3, 2, 2, 1]
else
[0, 1, 1, 0, 2, 1, 3, 3, 2, 2])))))
else
(if i.val < 7344 then
(if i.val < 7336 then
(if i.val < 7332 then
(if i.val < 7330 then
(if i.val < 7329 then
[0, 1, 1, 0, 2, 2, 1, 0, 3, 0]
else
[0, 1, 1, 0, 2, 2, 1, 1, 0, 3])
else
(if i.val < 7331 then
[0, 1, 1, 0, 2, 2, 1, 1, 3, 2]
else
[0, 1, 1, 0, 2, 2, 1, 3, 0, 1]))
else
(if i.val < 7334 then
(if i.val < 7333 then
[0, 1, 1, 0, 2, 2, 3, 0, 0, 2]
else
[0, 1, 1, 0, 2, 2, 3, 0, 1, 2])
else
(if i.val < 7335 then
[0, 1, 1, 0, 2, 3, 0, 1, 1, 2]
else
[0, 1, 1, 0, 2, 3, 0, 1, 2, 2])))
else
(if i.val < 7340 then
(if i.val < 7338 then
(if i.val < 7337 then
[0, 1, 1, 0, 2, 3, 2, 1, 0, 3]
else
[0, 1, 1, 0, 2, 3, 3, 0, 2, 2])
else
(if i.val < 7339 then
[0, 1, 1, 0, 3, 0, 0, 1, 1, 2]
else
[0, 1, 1, 0, 3, 0, 0, 2, 1, 1]))
else
(if i.val < 7342 then
(if i.val < 7341 then
[0, 1, 1, 0, 3, 0, 0, 2, 2, 1]
else
[0, 1, 1, 0, 3, 0, 0, 2, 3, 3])
else
(if i.val < 7343 then
[0, 1, 1, 0, 3, 0, 1, 1, 2, 3]
else
[0, 1, 1, 0, 3, 0, 1, 2, 1, 1]))))
else
(if i.val < 7352 then
(if i.val < 7348 then
(if i.val < 7346 then
(if i.val < 7345 then
[0, 1, 1, 0, 3, 0, 1, 2, 2, 1]
else
[0, 1, 1, 0, 3, 0, 1, 2, 3, 3])
else
(if i.val < 7347 then
[0, 1, 1, 0, 3, 0, 2, 1, 0, 0]
else
[0, 1, 1, 0, 3, 0, 2, 1, 1, 0]))
else
(if i.val < 7350 then
(if i.val < 7349 then
[0, 1, 1, 0, 3, 0, 2, 3, 3, 2]
else
[0, 1, 1, 0, 3, 2, 1, 0, 0, 3])
else
(if i.val < 7351 then
[0, 1, 1, 0, 3, 2, 1, 1, 0, 0]
else
[0, 1, 1, 0, 3, 2, 1, 1, 2, 3])))
else
(if i.val < 7356 then
(if i.val < 7354 then
(if i.val < 7353 then
[0, 1, 1, 0, 3, 2, 2, 1, 1, 3]
else
[0, 1, 1, 0, 3, 2, 2, 1, 3, 2])
else
(if i.val < 7355 then
[0, 1, 1, 0, 3, 2, 2, 3, 0, 0]
else
[0, 1, 1, 0, 3, 2, 2, 3, 0, 1]))
else
(if i.val < 7358 then
(if i.val < 7357 then
[0, 1, 1, 0, 3, 3, 0, 1, 2, 1]
else
[0, 1, 1, 0, 3, 3, 0, 1, 2, 2])
else
(if i.val < 7359 then
[0, 1, 1, 0, 3, 3, 0, 2, 2, 1]
else
[0, 1, 1, 2, 1, 0, 0, 1, 3, 2]))))))
else
(if i.val < 7392 then
(if i.val < 7376 then
(if i.val < 7368 then
(if i.val < 7364 then
(if i.val < 7362 then
(if i.val < 7361 then
[0, 1, 1, 2, 1, 0, 3, 0, 2, 2]
else
[0, 1, 1, 2, 1, 0, 3, 3, 0, 1])
else
(if i.val < 7363 then
[0, 1, 1, 2, 1, 0, 3, 3, 2, 2]
else
[0, 1, 1, 2, 1, 1, 0, 2, 3, 0]))
else
(if i.val < 7366 then
(if i.val < 7365 then
[0, 1, 1, 2, 1, 1, 0, 2, 3, 2]
else
[0, 1, 1, 2, 1, 1, 0, 3, 2, 1])
else
(if i.val < 7367 then
[0, 1, 1, 2, 1, 1, 2, 3, 0, 1]
else
[0, 1, 1, 2, 1, 1, 3, 2, 2, 1])))
else
(if i.val < 7372 then
(if i.val < 7370 then
(if i.val < 7369 then
[0, 1, 1, 2, 1, 3, 2, 2, 1, 3]
else
[0, 1, 1, 2, 1, 3, 3, 2, 2, 1])
else
(if i.val < 7371 then
[0, 1, 1, 2, 2, 1, 0, 3, 0, 1]
else
[0, 1, 1, 2, 2, 1, 0, 3, 2, 1]))
else
(if i.val < 7374 then
(if i.val < 7373 then
[0, 1, 1, 2, 2, 1, 0, 3, 3, 2]
else
[0, 1, 1, 2, 2, 1, 1, 0, 3, 3])
else
(if i.val < 7375 then
[0, 1, 1, 2, 2, 1, 1, 3, 0, 0]
else
[0, 1, 1, 2, 2, 1, 3, 0, 0, 2]))))
else
(if i.val < 7384 then
(if i.val < 7380 then
(if i.val < 7378 then
(if i.val < 7377 then
[0, 1, 1, 2, 2, 1, 3, 2, 1, 1]
else
[0, 1, 1, 2, 2, 1, 3, 3, 0, 1])
else
(if i.val < 7379 then
[0, 1, 1, 2, 2, 3, 0, 1, 2, 3]
else
[0, 1, 1, 2, 2, 3, 2, 2, 1, 3]))
else
(if i.val < 7382 then
(if i.val < 7381 then
[0, 1, 1, 2, 3, 0, 0, 2, 1, 1]
else
[0, 1, 1, 2, 3, 0, 1, 1, 2, 1])
else
(if i.val < 7383 then
[0, 1, 1, 2, 3, 0, 1, 1, 2, 3]
else
[0, 1, 1, 2, 3, 0, 1, 2, 2, 1])))
else
(if i.val < 7388 then
(if i.val < 7386 then
(if i.val < 7385 then
[0, 1, 1, 2, 3, 0, 1, 2, 2, 3]
else
[0, 1, 1, 2, 3, 0, 1, 2, 3, 0])
else
(if i.val < 7387 then
[0, 1, 1, 2, 3, 0, 2, 1, 0, 3]
else
[0, 1, 1, 2, 3, 0, 2, 1, 3, 3]))
else
(if i.val < 7390 then
(if i.val < 7389 then
[0, 1, 1, 2, 3, 2, 1, 1, 0, 0]
else
[0, 1, 1, 2, 3, 2, 2, 1, 1, 3])
else
(if i.val < 7391 then
[0, 1, 1, 2, 3, 2, 2, 1, 3, 0]
else
[0, 1, 1, 2, 3, 3, 0, 0, 2, 3])))))
else
(if i.val < 7408 then
(if i.val < 7400 then
(if i.val < 7396 then
(if i.val < 7394 then
(if i.val < 7393 then
[0, 1, 1, 2, 3, 3, 0, 1, 1, 2]
else
[0, 1, 1, 2, 3, 3, 0, 1, 2, 1])
else
(if i.val < 7395 then
[0, 1, 1, 2, 3, 3, 0, 1, 2, 2]
else
[0, 1, 1, 2, 3, 3, 2, 1, 0, 3]))
else
(if i.val < 7398 then
(if i.val < 7397 then
[0, 1, 1, 3, 0, 0, 1, 1, 2, 2]
else
[0, 1, 1, 3, 0, 0, 1, 2, 3, 3])
else
(if i.val < 7399 then
[0, 1, 1, 3, 0, 0, 2, 1, 1, 2]
else
[0, 1, 1, 3, 0, 0, 2, 2, 3, 3])))
else
(if i.val < 7404 then
(if i.val < 7402 then
(if i.val < 7401 then
[0, 1, 1, 3, 0, 1, 1, 0, 2, 1]
else
[0, 1, 1, 3, 0, 1, 1, 2, 1, 0])
else
(if i.val < 7403 then
[0, 1, 1, 3, 0, 1, 1, 2, 2, 3]
else
[0, 1, 1, 3, 0, 2, 1, 0, 3, 3]))
else
(if i.val < 7406 then
(if i.val < 7405 then
[0, 1, 1, 3, 0, 2, 1, 1, 3, 2]
else
[0, 1, 1, 3, 0, 2, 2, 1, 0, 0])
else
(if i.val < 7407 then
[0, 1, 1, 3, 0, 2, 2, 1, 0, 3]
else
[0, 1, 1, 3, 0, 2, 3, 3, 0, 2]))))
else
(if i.val < 7416 then
(if i.val < 7412 then
(if i.val < 7410 then
(if i.val < 7409 then
[0, 1, 1, 3, 0, 2, 3, 3, 2, 1]
else
[0, 1, 1, 3, 2, 1, 0, 3, 3, 2])
else
(if i.val < 7411 then
[0, 1, 1, 3, 2, 1, 1, 2, 3, 3]
else
[0, 1, 1, 3, 2, 2, 1, 0, 0, 3]))
else
(if i.val < 7414 then
(if i.val < 7413 then
[0, 1, 1, 3, 2, 2, 1, 0, 3, 2]
else
[0, 1, 1, 3, 2, 2, 3, 0, 1, 1])
else
(if i.val < 7415 then
[0, 1, 1, 3, 3, 0, 1, 1, 0, 2]
else
[0, 1, 1, 3, 3, 0, 1, 2, 1, 1])))
else
(if i.val < 7420 then
(if i.val < 7418 then
(if i.val < 7417 then
[0, 1, 1, 3, 3, 0, 1, 2, 2, 1]
else
[0, 1, 1, 3, 3, 0, 2, 2, 1, 1])
else
(if i.val < 7419 then
[0, 1, 1, 3, 3, 0, 2, 3, 3, 2]
else
[0, 1, 2, 1, 0, 0, 1, 2, 3, 0]))
else
(if i.val < 7422 then
(if i.val < 7421 then
[0, 1, 2, 1, 0, 0, 3, 2, 2, 1]
else
[0, 1, 2, 1, 0, 3, 3, 0, 2, 2])
else
(if i.val < 7423 then
[0, 1, 2, 1, 0, 3, 3, 2, 1, 1]
else
[0, 1, 2, 1, 1, 0, 0, 3, 2, 2])))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row31_cosetWordsPart0058 : Fin 8640 → List (Fin 4) :=
  fun i => (if i.val < 7488 then
(if i.val < 7456 then
(if i.val < 7440 then
(if i.val < 7432 then
(if i.val < 7428 then
(if i.val < 7426 then
(if i.val < 7425 then
[0, 1, 2, 1, 1, 0, 2, 1, 3, 0]
else
[0, 1, 2, 1, 1, 0, 2, 1, 3, 2])
else
(if i.val < 7427 then
[0, 1, 2, 1, 1, 0, 2, 3, 0, 0]
else
[0, 1, 2, 1, 1, 0, 2, 3, 0, 1]))
else
(if i.val < 7430 then
(if i.val < 7429 then
[0, 1, 2, 1, 1, 0, 2, 3, 0, 2]
else
[0, 1, 2, 1, 1, 0, 3, 0, 2, 3])
else
(if i.val < 7431 then
[0, 1, 2, 1, 1, 2, 3, 0, 0, 2]
else
[0, 1, 2, 1, 1, 2, 3, 3, 0, 0])))
else
(if i.val < 7436 then
(if i.val < 7434 then
(if i.val < 7433 then
[0, 1, 2, 1, 1, 3, 0, 1, 1, 2]
else
[0, 1, 2, 1, 1, 3, 0, 1, 2, 1])
else
(if i.val < 7435 then
[0, 1, 2, 1, 1, 3, 0, 1, 2, 2]
else
[0, 1, 2, 1, 1, 3, 0, 1, 2, 3]))
else
(if i.val < 7438 then
(if i.val < 7437 then
[0, 1, 2, 1, 1, 3, 0, 2, 2, 3]
else
[0, 1, 2, 1, 1, 3, 2, 2, 1, 1])
else
(if i.val < 7439 then
[0, 1, 2, 1, 1, 3, 2, 2, 3, 0]
else
[0, 1, 2, 1, 3, 0, 0, 1, 2, 3]))))
else
(if i.val < 7448 then
(if i.val < 7444 then
(if i.val < 7442 then
(if i.val < 7441 then
[0, 1, 2, 1, 3, 0, 0, 2, 2, 3]
else
[0, 1, 2, 1, 3, 0, 0, 3, 2, 2])
else
(if i.val < 7443 then
[0, 1, 2, 1, 3, 0, 1, 2, 2, 3]
else
[0, 1, 2, 1, 3, 0, 1, 2, 3, 0]))
else
(if i.val < 7446 then
(if i.val < 7445 then
[0, 1, 2, 1, 3, 2, 1, 0, 3, 2]
else
[0, 1, 2, 1, 3, 2, 2, 1, 0, 0])
else
(if i.val < 7447 then
[0, 1, 2, 1, 3, 2, 2, 1, 1, 3]
else
[0, 1, 2, 1, 3, 3, 0, 0, 2, 2])))
else
(if i.val < 7452 then
(if i.val < 7450 then
(if i.val < 7449 then
[0, 1, 2, 1, 3, 3, 0, 1, 2, 1]
else
[0, 1, 2, 1, 3, 3, 0, 1, 2, 2])
else
(if i.val < 7451 then
[0, 1, 2, 1, 3, 3, 0, 1, 2, 3]
else
[0, 1, 2, 1, 3, 3, 0, 2, 2, 1]))
else
(if i.val < 7454 then
(if i.val < 7453 then
[0, 1, 2, 1, 3, 3, 0, 2, 2, 3]
else
[0, 1, 2, 1, 3, 3, 2, 2, 1, 1])
else
(if i.val < 7455 then
[0, 1, 2, 2, 1, 0, 3, 0, 2, 1]
else
[0, 1, 2, 2, 1, 0, 3, 0, 2, 3])))))
else
(if i.val < 7472 then
(if i.val < 7464 then
(if i.val < 7460 then
(if i.val < 7458 then
(if i.val < 7457 then
[0, 1, 2, 2, 1, 0, 3, 2, 1, 1]
else
[0, 1, 2, 2, 1, 0, 3, 3, 0, 1])
else
(if i.val < 7459 then
[0, 1, 2, 2, 1, 1, 0, 3, 0, 2]
else
[0, 1, 2, 2, 1, 1, 0, 3, 2, 1]))
else
(if i.val < 7462 then
(if i.val < 7461 then
[0, 1, 2, 2, 1, 1, 3, 0, 2, 1]
else
[0, 1, 2, 2, 1, 1, 3, 2, 1, 0])
else
(if i.val < 7463 then
[0, 1, 2, 2, 1, 1, 3, 2, 1, 1]
else
[0, 1, 2, 2, 1, 3, 0, 0, 1, 2])))
else
(if i.val < 7468 then
(if i.val < 7466 then
(if i.val < 7465 then
[0, 1, 2, 2, 1, 3, 0, 0, 2, 3]
else
[0, 1, 2, 2, 1, 3, 0, 1, 2, 1])
else
(if i.val < 7467 then
[0, 1, 2, 2, 1, 3, 3, 0, 1, 2]
else
[0, 1, 2, 2, 3, 0, 0, 1, 1, 2]))
else
(if i.val < 7470 then
(if i.val < 7469 then
[0, 1, 2, 2, 3, 0, 1, 2, 3, 0]
else
[0, 1, 2, 2, 3, 0, 1, 2, 3, 3])
else
(if i.val < 7471 then
[0, 1, 2, 2, 3, 0, 2, 2, 1, 3]
else
[0, 1, 2, 2, 3, 0, 2, 2, 3, 3]))))
else
(if i.val < 7480 then
(if i.val < 7476 then
(if i.val < 7474 then
(if i.val < 7473 then
[0, 1, 2, 2, 3, 0, 2, 3, 3, 2]
else
[0, 1, 2, 2, 3, 2, 2, 1, 1, 3])
else
(if i.val < 7475 then
[0, 1, 2, 2, 3, 2, 2, 3, 0, 1]
else
[0, 1, 2, 2, 3, 3, 2, 2, 1, 1]))
else
(if i.val < 7478 then
(if i.val < 7477 then
[0, 1, 2, 3, 0, 0, 1, 1, 2, 1]
else
[0, 1, 2, 3, 0, 0, 1, 1, 2, 3])
else
(if i.val < 7479 then
[0, 1, 2, 3, 0, 0, 2, 1, 1, 2]
else
[0, 1, 2, 3, 0, 0, 2, 2, 1, 1])))
else
(if i.val < 7484 then
(if i.val < 7482 then
(if i.val < 7481 then
[0, 1, 2, 3, 0, 0, 2, 3, 3, 2]
else
[0, 1, 2, 3, 0, 0, 3, 2, 2, 1])
else
(if i.val < 7483 then
[0, 1, 2, 3, 0, 1, 1, 2, 1, 1]
else
[0, 1, 2, 3, 0, 1, 1, 2, 3, 3]))
else
(if i.val < 7486 then
(if i.val < 7485 then
[0, 1, 2, 3, 0, 1, 2, 1, 1, 0]
else
[0, 1, 2, 3, 0, 1, 2, 1, 3, 2])
else
(if i.val < 7487 then
[0, 1, 2, 3, 0, 1, 2, 2, 1, 1]
else
[0, 1, 2, 3, 0, 1, 2, 2, 1, 3]))))))
else
(if i.val < 7520 then
(if i.val < 7504 then
(if i.val < 7496 then
(if i.val < 7492 then
(if i.val < 7490 then
(if i.val < 7489 then
[0, 1, 2, 3, 0, 1, 2, 2, 3, 0]
else
[0, 1, 2, 3, 0, 2, 2, 1, 0, 0])
else
(if i.val < 7491 then
[0, 1, 2, 3, 0, 2, 2, 1, 0, 3]
else
[0, 1, 2, 3, 0, 2, 2, 1, 3, 3]))
else
(if i.val < 7494 then
(if i.val < 7493 then
[0, 1, 2, 3, 2, 1, 0, 3, 2, 2]
else
[0, 1, 2, 3, 2, 2, 1, 3, 2, 2])
else
(if i.val < 7495 then
[0, 1, 2, 3, 3, 0, 0, 2, 2, 3]
else
[0, 1, 2, 3, 3, 0, 1, 2, 1, 0])))
else
(if i.val < 7500 then
(if i.val < 7498 then
(if i.val < 7497 then
[0, 1, 2, 3, 3, 0, 1, 2, 1, 1]
else
[0, 1, 2, 3, 3, 0, 1, 2, 1, 3])
else
(if i.val < 7499 then
[0, 1, 2, 3, 3, 0, 1, 2, 3, 0]
else
[0, 1, 2, 3, 3, 0, 1, 2, 3, 3]))
else
(if i.val < 7502 then
(if i.val < 7501 then
[0, 1, 2, 3, 3, 2, 1, 0, 0, 3]
else
[0, 1, 3, 0, 0, 1, 1, 2, 1, 0])
else
(if i.val < 7503 then
[0, 1, 3, 0, 0, 1, 1, 2, 1, 1]
else
[0, 1, 3, 0, 0, 1, 1, 2, 2, 1]))))
else
(if i.val < 7512 then
(if i.val < 7508 then
(if i.val < 7506 then
(if i.val < 7505 then
[0, 1, 3, 0, 0, 1, 1, 2, 2, 3]
else
[0, 1, 3, 0, 0, 1, 1, 2, 3, 2])
else
(if i.val < 7507 then
[0, 1, 3, 0, 0, 1, 1, 2, 3, 3]
else
[0, 1, 3, 0, 0, 1, 2, 1, 1, 2]))
else
(if i.val < 7510 then
(if i.val < 7509 then
[0, 1, 3, 0, 0, 1, 2, 2, 1, 1]
else
[0, 1, 3, 0, 0, 1, 2, 2, 1, 3])
else
(if i.val < 7511 then
[0, 1, 3, 0, 0, 1, 2, 2, 3, 3]
else
[0, 1, 3, 0, 0, 1, 2, 3, 3, 2])))
else
(if i.val < 7516 then
(if i.val < 7514 then
(if i.val < 7513 then
[0, 1, 3, 0, 0, 2, 2, 3, 2, 2]
else
[0, 1, 3, 0, 0, 2, 2, 3, 3, 2])
else
(if i.val < 7515 then
[0, 1, 3, 0, 0, 3, 2, 2, 1, 3]
else
[0, 1, 3, 0, 1, 2, 1, 0, 3, 2]))
else
(if i.val < 7518 then
(if i.val < 7517 then
[0, 1, 3, 0, 1, 2, 1, 1, 3, 3]
else
[0, 1, 3, 0, 2, 1, 0, 3, 2, 2])
else
(if i.val < 7519 then
[0, 1, 3, 0, 2, 1, 1, 3, 2, 2]
else
[0, 1, 3, 0, 2, 2, 1, 3, 3, 2])))))
else
(if i.val < 7536 then
(if i.val < 7528 then
(if i.val < 7524 then
(if i.val < 7522 then
(if i.val < 7521 then
[0, 1, 3, 2, 1, 1, 0, 0, 2, 3]
else
[0, 1, 3, 2, 1, 1, 0, 0, 3, 2])
else
(if i.val < 7523 then
[0, 1, 3, 2, 1, 1, 0, 2, 3, 0]
else
[0, 1, 3, 2, 1, 1, 2, 3, 3, 2]))
else
(if i.val < 7526 then
(if i.val < 7525 then
[0, 1, 3, 2, 2, 1, 0, 3, 2, 1]
else
[0, 1, 3, 2, 2, 1, 3, 0, 1, 2])
else
(if i.val < 7527 then
[0, 1, 3, 2, 2, 3, 0, 0, 1, 2]
else
[0, 1, 3, 2, 2, 3, 0, 1, 2, 3])))
else
(if i.val < 7532 then
(if i.val < 7530 then
(if i.val < 7529 then
[0, 1, 3, 3, 0, 0, 1, 1, 2, 2]
else
[0, 1, 3, 3, 0, 0, 1, 1, 2, 3])
else
(if i.val < 7531 then
[0, 1, 3, 3, 0, 0, 2, 2, 1, 3]
else
[0, 1, 3, 3, 0, 0, 2, 3, 3, 2]))
else
(if i.val < 7534 then
(if i.val < 7533 then
[0, 1, 3, 3, 0, 1, 2, 1, 0, 0]
else
[0, 1, 3, 3, 0, 1, 2, 1, 1, 0])
else
(if i.val < 7535 then
[0, 1, 3, 3, 0, 1, 2, 2, 1, 0]
else
[0, 1, 3, 3, 0, 2, 1, 0, 3, 3]))))
else
(if i.val < 7544 then
(if i.val < 7540 then
(if i.val < 7538 then
(if i.val < 7537 then
[0, 1, 3, 3, 0, 2, 1, 1, 2, 3]
else
[0, 1, 3, 3, 0, 2, 1, 3, 3, 2])
else
(if i.val < 7539 then
[0, 1, 3, 3, 0, 2, 2, 1, 0, 3]
else
[0, 1, 3, 3, 0, 2, 3, 3, 0, 2]))
else
(if i.val < 7542 then
(if i.val < 7541 then
[0, 1, 3, 3, 2, 1, 0, 3, 2, 2]
else
[0, 1, 3, 3, 2, 1, 0, 3, 3, 2])
else
(if i.val < 7543 then
[0, 1, 3, 3, 2, 1, 1, 0, 2, 3]
else
[0, 1, 3, 3, 2, 2, 1, 0, 0, 3])))
else
(if i.val < 7548 then
(if i.val < 7546 then
(if i.val < 7545 then
[0, 2, 1, 0, 0, 1, 2, 2, 3, 0]
else
[0, 2, 1, 0, 0, 1, 2, 2, 3, 3])
else
(if i.val < 7547 then
[0, 2, 1, 0, 0, 1, 2, 3, 0, 1]
else
[0, 2, 1, 0, 0, 1, 3, 0, 2, 2]))
else
(if i.val < 7550 then
(if i.val < 7549 then
[0, 2, 1, 0, 0, 1, 3, 2, 2, 3]
else
[0, 2, 1, 0, 0, 3, 0, 0, 3, 2])
else
(if i.val < 7551 then
[0, 2, 1, 0, 3, 0, 0, 1, 1, 2]
else
[0, 2, 1, 0, 3, 0, 0, 1, 2, 1])))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row31_cosetWordsPart0059 : Fin 8640 → List (Fin 4) :=
  fun i => (if i.val < 7616 then
(if i.val < 7584 then
(if i.val < 7568 then
(if i.val < 7560 then
(if i.val < 7556 then
(if i.val < 7554 then
(if i.val < 7553 then
[0, 2, 1, 0, 3, 0, 2, 1, 0, 0]
else
[0, 2, 1, 0, 3, 0, 2, 2, 1, 3])
else
(if i.val < 7555 then
[0, 2, 1, 0, 3, 0, 2, 2, 3, 0]
else
[0, 2, 1, 0, 3, 0, 2, 2, 3, 3]))
else
(if i.val < 7558 then
(if i.val < 7557 then
[0, 2, 1, 0, 3, 0, 2, 3, 3, 0]
else
[0, 2, 1, 0, 3, 2, 1, 1, 0, 0])
else
(if i.val < 7559 then
[0, 2, 1, 0, 3, 2, 1, 1, 2, 3]
else
[0, 2, 1, 0, 3, 3, 0, 0, 2, 1])))
else
(if i.val < 7564 then
(if i.val < 7562 then
(if i.val < 7561 then
[0, 2, 1, 0, 3, 3, 0, 0, 2, 2]
else
[0, 2, 1, 0, 3, 3, 0, 1, 2, 1])
else
(if i.val < 7563 then
[0, 2, 1, 0, 3, 3, 0, 1, 2, 3]
else
[0, 2, 1, 0, 3, 3, 0, 2, 2, 1]))
else
(if i.val < 7566 then
(if i.val < 7565 then
[0, 2, 1, 0, 3, 3, 2, 2, 1, 1]
else
[0, 2, 1, 1, 0, 0, 2, 1, 3, 3])
else
(if i.val < 7567 then
[0, 2, 1, 1, 0, 0, 2, 3, 3, 2]
else
[0, 2, 1, 1, 0, 2, 1, 3, 0, 1]))))
else
(if i.val < 7576 then
(if i.val < 7572 then
(if i.val < 7570 then
(if i.val < 7569 then
[0, 2, 1, 1, 0, 2, 3, 0, 0, 3]
else
[0, 2, 1, 1, 0, 2, 3, 0, 2, 1])
else
(if i.val < 7571 then
[0, 2, 1, 1, 0, 2, 3, 2, 1, 1]
else
[0, 2, 1, 1, 0, 3, 0, 1, 2, 1]))
else
(if i.val < 7574 then
(if i.val < 7573 then
[0, 2, 1, 1, 0, 3, 0, 2, 1, 0]
else
[0, 2, 1, 1, 0, 3, 0, 2, 2, 3])
else
(if i.val < 7575 then
[0, 2, 1, 1, 0, 3, 2, 1, 1, 0]
else
[0, 2, 1, 1, 0, 3, 3, 0, 2, 2])))
else
(if i.val < 7580 then
(if i.val < 7578 then
(if i.val < 7577 then
[0, 2, 1, 1, 0, 3, 3, 0, 2, 3]
else
[0, 2, 1, 1, 2, 3, 2, 2, 1, 3])
else
(if i.val < 7579 then
[0, 2, 1, 1, 3, 0, 0, 1, 2, 1]
else
[0, 2, 1, 1, 3, 0, 1, 1, 2, 1]))
else
(if i.val < 7582 then
(if i.val < 7581 then
[0, 2, 1, 1, 3, 0, 1, 1, 2, 2]
else
[0, 2, 1, 1, 3, 0, 1, 2, 2, 1])
else
(if i.val < 7583 then
[0, 2, 1, 1, 3, 0, 2, 1, 1, 2]
else
[0, 2, 1, 1, 3, 0, 2, 2, 1, 1])))))
else
(if i.val < 7600 then
(if i.val < 7592 then
(if i.val < 7588 then
(if i.val < 7586 then
(if i.val < 7585 then
[0, 2, 1, 1, 3, 0, 2, 2, 3, 0]
else
[0, 2, 1, 1, 3, 0, 2, 3, 3, 2])
else
(if i.val < 7587 then
[0, 2, 1, 1, 3, 2, 1, 1, 0, 0]
else
[0, 2, 1, 1, 3, 2, 2, 1, 0, 0]))
else
(if i.val < 7590 then
(if i.val < 7589 then
[0, 2, 1, 1, 3, 2, 2, 1, 1, 3]
else
[0, 2, 1, 1, 3, 2, 2, 1, 3, 0])
else
(if i.val < 7591 then
[0, 2, 1, 1, 3, 2, 2, 3, 0, 1]
else
[0, 2, 1, 1, 3, 3, 2, 1, 0, 0])))
else
(if i.val < 7596 then
(if i.val < 7594 then
(if i.val < 7593 then
[0, 2, 1, 3, 0, 0, 1, 2, 2, 3]
else
[0, 2, 1, 3, 0, 0, 2, 1, 1, 2])
else
(if i.val < 7595 then
[0, 2, 1, 3, 0, 0, 3, 2, 2, 1]
else
[0, 2, 1, 3, 0, 1, 2, 1, 3, 0]))
else
(if i.val < 7598 then
(if i.val < 7597 then
[0, 2, 1, 3, 0, 1, 2, 2, 1, 0]
else
[0, 2, 1, 3, 0, 1, 2, 2, 1, 1])
else
(if i.val < 7599 then
[0, 2, 1, 3, 0, 1, 2, 2, 1, 3]
else
[0, 2, 1, 3, 3, 0, 0, 1, 1, 2]))))
else
(if i.val < 7608 then
(if i.val < 7604 then
(if i.val < 7602 then
(if i.val < 7601 then
[0, 2, 1, 3, 3, 0, 0, 1, 2, 3]
else
[0, 2, 1, 3, 3, 0, 0, 2, 2, 3])
else
(if i.val < 7603 then
[0, 2, 1, 3, 3, 0, 1, 2, 1, 0]
else
[0, 2, 1, 3, 3, 0, 1, 2, 2, 3]))
else
(if i.val < 7606 then
(if i.val < 7605 then
[0, 2, 1, 3, 3, 0, 1, 2, 3, 0]
else
[0, 2, 1, 3, 3, 0, 2, 1, 1, 2])
else
(if i.val < 7607 then
[0, 2, 1, 3, 3, 0, 2, 2, 1, 0]
else
[0, 2, 1, 3, 3, 0, 2, 2, 1, 3])))
else
(if i.val < 7612 then
(if i.val < 7610 then
(if i.val < 7609 then
[0, 2, 2, 1, 0, 0, 1, 2, 3, 3]
else
[0, 2, 2, 1, 0, 0, 1, 3, 0, 2])
else
(if i.val < 7611 then
[0, 2, 2, 1, 0, 0, 3, 2, 2, 1]
else
[0, 2, 2, 1, 0, 0, 3, 3, 2, 1]))
else
(if i.val < 7614 then
(if i.val < 7613 then
[0, 2, 2, 1, 0, 0, 3, 3, 2, 2]
else
[0, 2, 2, 1, 0, 3, 0, 0, 2, 1])
else
(if i.val < 7615 then
[0, 2, 2, 1, 0, 3, 0, 0, 3, 2]
else
[0, 2, 2, 1, 1, 0, 3, 0, 0, 2]))))))
else
(if i.val < 7648 then
(if i.val < 7632 then
(if i.val < 7624 then
(if i.val < 7620 then
(if i.val < 7618 then
(if i.val < 7617 then
[0, 2, 2, 1, 1, 0, 3, 0, 2, 1]
else
[0, 2, 2, 1, 1, 0, 3, 2, 1, 0])
else
(if i.val < 7619 then
[0, 2, 2, 1, 1, 0, 3, 2, 1, 1]
else
[0, 2, 2, 1, 1, 3, 0, 1, 2, 1]))
else
(if i.val < 7622 then
(if i.val < 7621 then
[0, 2, 2, 1, 1, 3, 0, 2, 1, 0]
else
[0, 2, 2, 1, 1, 3, 2, 1, 0, 0])
else
(if i.val < 7623 then
[0, 2, 2, 1, 3, 0, 1, 2, 1, 1]
else
[0, 2, 2, 1, 3, 0, 1, 2, 3, 0])))
else
(if i.val < 7628 then
(if i.val < 7626 then
(if i.val < 7625 then
[0, 2, 2, 1, 3, 0, 1, 2, 3, 3]
else
[0, 2, 2, 1, 3, 2, 1, 1, 0, 0])
else
(if i.val < 7627 then
[0, 2, 2, 1, 3, 3, 0, 0, 2, 3]
else
[0, 2, 2, 1, 3, 3, 0, 1, 2, 1]))
else
(if i.val < 7630 then
(if i.val < 7629 then
[0, 2, 2, 1, 3, 3, 0, 1, 2, 3]
else
[0, 2, 2, 1, 3, 3, 0, 2, 1, 1])
else
(if i.val < 7631 then
[0, 2, 2, 1, 3, 3, 2, 1, 0, 0]
else
[0, 2, 2, 1, 3, 3, 2, 1, 0, 3]))))
else
(if i.val < 7640 then
(if i.val < 7636 then
(if i.val < 7634 then
(if i.val < 7633 then
[0, 2, 2, 3, 0, 0, 2, 1, 1, 2]
else
[0, 2, 2, 3, 0, 0, 2, 2, 3, 0])
else
(if i.val < 7635 then
[0, 2, 2, 3, 0, 0, 3, 2, 1, 0]
else
[0, 2, 2, 3, 0, 1, 1, 0, 3, 2]))
else
(if i.val < 7638 then
(if i.val < 7637 then
[0, 2, 2, 3, 0, 1, 2, 3, 0, 1]
else
[0, 2, 2, 3, 0, 1, 2, 3, 3, 0])
else
(if i.val < 7639 then
[0, 2, 2, 3, 0, 1, 2, 3, 3, 2]
else
[0, 2, 2, 3, 0, 2, 2, 1, 0, 3])))
else
(if i.val < 7644 then
(if i.val < 7642 then
(if i.val < 7641 then
[0, 2, 2, 3, 0, 2, 3, 3, 0, 2]
else
[0, 2, 2, 3, 0, 2, 3, 3, 2, 1])
else
(if i.val < 7643 then
[0, 2, 2, 3, 2, 1, 0, 3, 2, 2]
else
[0, 2, 2, 3, 2, 2, 1, 0, 3, 0]))
else
(if i.val < 7646 then
(if i.val < 7645 then
[0, 2, 2, 3, 2, 2, 1, 3, 0, 0]
else
[0, 2, 2, 3, 3, 0, 1, 2, 1, 1])
else
(if i.val < 7647 then
[0, 2, 2, 3, 3, 0, 1, 2, 1, 3]
else
[0, 2, 2, 3, 3, 0, 1, 2, 3, 0])))))
else
(if i.val < 7664 then
(if i.val < 7656 then
(if i.val < 7652 then
(if i.val < 7650 then
(if i.val < 7649 then
[0, 2, 2, 3, 3, 0, 2, 3, 3, 2]
else
[0, 2, 3, 0, 0, 1, 1, 2, 1, 3])
else
(if i.val < 7651 then
[0, 2, 3, 0, 0, 1, 1, 2, 2, 1]
else
[0, 2, 3, 0, 0, 1, 1, 2, 3, 3]))
else
(if i.val < 7654 then
(if i.val < 7653 then
[0, 2, 3, 0, 0, 1, 3, 2, 2, 1]
else
[0, 2, 3, 0, 0, 2, 2, 3, 0, 0])
else
(if i.val < 7655 then
[0, 2, 3, 0, 0, 2, 3, 3, 2, 1]
else
[0, 2, 3, 0, 0, 3, 2, 1, 0, 0])))
else
(if i.val < 7660 then
(if i.val < 7658 then
(if i.val < 7657 then
[0, 2, 3, 0, 0, 3, 2, 1, 1, 0]
else
[0, 2, 3, 0, 0, 3, 2, 2, 3, 0])
else
(if i.val < 7659 then
[0, 2, 3, 0, 1, 1, 0, 2, 3, 2]
else
[0, 2, 3, 0, 1, 1, 0, 2, 3, 3]))
else
(if i.val < 7662 then
(if i.val < 7661 then
[0, 2, 3, 0, 1, 1, 0, 3, 2, 1]
else
[0, 2, 3, 0, 1, 1, 2, 1, 0, 3])
else
(if i.val < 7663 then
[0, 2, 3, 0, 1, 1, 2, 2, 1, 1]
else
[0, 2, 3, 0, 1, 1, 2, 2, 3, 0]))))
else
(if i.val < 7672 then
(if i.val < 7668 then
(if i.val < 7666 then
(if i.val < 7665 then
[0, 2, 3, 0, 1, 1, 2, 2, 3, 3]
else
[0, 2, 3, 0, 1, 1, 2, 3, 0, 1])
else
(if i.val < 7667 then
[0, 2, 3, 0, 1, 1, 2, 3, 3, 0]
else
[0, 2, 3, 0, 1, 2, 1, 1, 0, 3]))
else
(if i.val < 7670 then
(if i.val < 7669 then
[0, 2, 3, 0, 1, 2, 1, 1, 3, 2]
else
[0, 2, 3, 0, 1, 2, 1, 3, 2, 2])
else
(if i.val < 7671 then
[0, 2, 3, 0, 1, 2, 2, 1, 3, 3]
else
[0, 2, 3, 0, 1, 2, 2, 3, 0, 0])))
else
(if i.val < 7676 then
(if i.val < 7674 then
(if i.val < 7673 then
[0, 2, 3, 0, 1, 2, 2, 3, 3, 0]
else
[0, 2, 3, 0, 2, 1, 1, 2, 3, 0])
else
(if i.val < 7675 then
[0, 2, 3, 0, 2, 1, 3, 2, 2, 1]
else
[0, 2, 3, 0, 2, 1, 3, 2, 2, 3]))
else
(if i.val < 7678 then
(if i.val < 7677 then
[0, 2, 3, 0, 2, 1, 3, 3, 0, 1]
else
[0, 2, 3, 0, 2, 2, 1, 1, 3, 3])
else
(if i.val < 7679 then
[0, 2, 3, 0, 2, 2, 1, 3, 0, 2]
else
[0, 2, 3, 0, 2, 2, 1, 3, 3, 2])))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row31_cosetWordsPart0060 : Fin 8640 → List (Fin 4) :=
  fun i => (if i.val < 7744 then
(if i.val < 7712 then
(if i.val < 7696 then
(if i.val < 7688 then
(if i.val < 7684 then
(if i.val < 7682 then
(if i.val < 7681 then
[0, 2, 3, 2, 1, 0, 0, 1, 2, 2]
else
[0, 2, 3, 2, 1, 0, 0, 3, 2, 1])
else
(if i.val < 7683 then
[0, 2, 3, 2, 1, 0, 3, 2, 2, 1]
else
[0, 2, 3, 2, 1, 1, 0, 2, 3, 2]))
else
(if i.val < 7686 then
(if i.val < 7685 then
[0, 2, 3, 2, 1, 1, 0, 3, 2, 1]
else
[0, 2, 3, 2, 2, 1, 1, 0, 3, 2])
else
(if i.val < 7687 then
[0, 2, 3, 2, 2, 1, 1, 0, 3, 3]
else
[0, 2, 3, 2, 2, 1, 3, 0, 1, 2])))
else
(if i.val < 7692 then
(if i.val < 7690 then
(if i.val < 7689 then
[0, 2, 3, 2, 2, 1, 3, 2, 2, 1]
else
[0, 2, 3, 2, 2, 3, 0, 0, 3, 2])
else
(if i.val < 7691 then
[0, 2, 3, 2, 2, 3, 0, 1, 2, 3]
else
[0, 2, 3, 3, 0, 0, 2, 1, 3, 3]))
else
(if i.val < 7694 then
(if i.val < 7693 then
[0, 2, 3, 3, 0, 1, 1, 0, 2, 2]
else
[0, 2, 3, 3, 0, 1, 1, 0, 2, 3])
else
(if i.val < 7695 then
[0, 2, 3, 3, 0, 1, 1, 0, 3, 2]
else
[0, 2, 3, 3, 0, 1, 1, 2, 2, 1]))))
else
(if i.val < 7704 then
(if i.val < 7700 then
(if i.val < 7698 then
(if i.val < 7697 then
[0, 2, 3, 3, 0, 1, 1, 2, 2, 3]
else
[0, 2, 3, 3, 0, 1, 2, 1, 1, 0])
else
(if i.val < 7699 then
[0, 2, 3, 3, 0, 1, 2, 1, 1, 3]
else
[0, 2, 3, 3, 0, 1, 2, 1, 3, 3]))
else
(if i.val < 7702 then
(if i.val < 7701 then
[0, 2, 3, 3, 0, 1, 2, 2, 1, 1]
else
[0, 2, 3, 3, 0, 1, 2, 3, 0, 0])
else
(if i.val < 7703 then
[0, 2, 3, 3, 0, 2, 1, 0, 3, 0]
else
[0, 2, 3, 3, 0, 2, 1, 1, 3, 2])))
else
(if i.val < 7708 then
(if i.val < 7706 then
(if i.val < 7705 then
[0, 2, 3, 3, 0, 2, 2, 1, 3, 0]
else
[0, 2, 3, 3, 0, 2, 3, 3, 0, 2])
else
(if i.val < 7707 then
[0, 2, 3, 3, 0, 2, 3, 3, 2, 1]
else
[0, 2, 3, 3, 2, 1, 0, 3, 2, 2]))
else
(if i.val < 7710 then
(if i.val < 7709 then
[0, 2, 3, 3, 2, 2, 1, 1, 0, 0]
else
[0, 3, 0, 0, 1, 1, 2, 1, 3, 3])
else
(if i.val < 7711 then
[0, 3, 0, 0, 1, 1, 2, 2, 1, 0]
else
[0, 3, 0, 0, 1, 1, 2, 2, 1, 1])))))
else
(if i.val < 7728 then
(if i.val < 7720 then
(if i.val < 7716 then
(if i.val < 7714 then
(if i.val < 7713 then
[0, 3, 0, 0, 1, 1, 2, 2, 1, 3]
else
[0, 3, 0, 0, 1, 2, 3, 0, 0, 2])
else
(if i.val < 7715 then
[0, 3, 0, 0, 1, 2, 3, 3, 2, 1]
else
[0, 3, 0, 0, 1, 3, 0, 2, 1, 1]))
else
(if i.val < 7718 then
(if i.val < 7717 then
[0, 3, 0, 0, 2, 1, 0, 3, 2, 2]
else
[0, 3, 0, 0, 2, 1, 1, 2, 3, 0])
else
(if i.val < 7719 then
[0, 3, 0, 0, 2, 1, 1, 2, 3, 2]
else
[0, 3, 0, 0, 2, 2, 1, 1, 3, 2])))
else
(if i.val < 7724 then
(if i.val < 7722 then
(if i.val < 7721 then
[0, 3, 0, 0, 2, 2, 1, 3, 0, 0]
else
[0, 3, 0, 0, 2, 2, 3, 0, 2, 2])
else
(if i.val < 7723 then
[0, 3, 0, 0, 2, 2, 3, 2, 1, 1]
else
[0, 3, 0, 0, 2, 2, 3, 2, 2, 1]))
else
(if i.val < 7726 then
(if i.val < 7725 then
[0, 3, 0, 0, 2, 3, 2, 1, 0, 0]
else
[0, 3, 0, 0, 2, 3, 3, 2, 1, 0])
else
(if i.val < 7727 then
[0, 3, 0, 0, 3, 2, 2, 1, 1, 0]
else
[0, 3, 0, 0, 3, 2, 2, 1, 3, 0]))))
else
(if i.val < 7736 then
(if i.val < 7732 then
(if i.val < 7730 then
(if i.val < 7729 then
[0, 3, 0, 0, 3, 2, 2, 3, 0, 0]
else
[0, 3, 0, 1, 1, 0, 2, 1, 0, 0])
else
(if i.val < 7731 then
[0, 3, 0, 1, 1, 0, 2, 1, 1, 2]
else
[0, 3, 0, 1, 1, 0, 2, 2, 1, 0]))
else
(if i.val < 7734 then
(if i.val < 7733 then
[0, 3, 0, 1, 1, 0, 2, 2, 3, 3]
else
[0, 3, 0, 1, 1, 0, 3, 2, 2, 1])
else
(if i.val < 7735 then
[0, 3, 0, 1, 1, 2, 3, 3, 0, 1]
else
[0, 3, 0, 1, 2, 1, 1, 0, 0, 2])))
else
(if i.val < 7740 then
(if i.val < 7738 then
(if i.val < 7737 then
[0, 3, 0, 1, 2, 1, 1, 0, 2, 3]
else
[0, 3, 0, 1, 2, 1, 3, 3, 2, 2])
else
(if i.val < 7739 then
[0, 3, 0, 1, 2, 2, 1, 1, 3, 2]
else
[0, 3, 0, 1, 2, 2, 1, 3, 3, 2]))
else
(if i.val < 7742 then
(if i.val < 7741 then
[0, 3, 0, 1, 2, 2, 3, 3, 0, 0]
else
[0, 3, 0, 1, 2, 3, 3, 0, 1, 2])
else
(if i.val < 7743 then
[0, 3, 0, 1, 2, 3, 3, 2, 1, 1]
else
[0, 3, 0, 2, 1, 0, 3, 2, 2, 3]))))))
else
(if i.val < 7776 then
(if i.val < 7760 then
(if i.val < 7752 then
(if i.val < 7748 then
(if i.val < 7746 then
(if i.val < 7745 then
[0, 3, 0, 2, 1, 0, 3, 3, 0, 1]
else
[0, 3, 0, 2, 1, 1, 0, 0, 2, 1])
else
(if i.val < 7747 then
[0, 3, 0, 2, 1, 1, 0, 0, 2, 3]
else
[0, 3, 0, 2, 1, 1, 0, 2, 3, 2]))
else
(if i.val < 7750 then
(if i.val < 7749 then
[0, 3, 0, 2, 1, 1, 0, 2, 3, 3]
else
[0, 3, 0, 2, 1, 1, 0, 3, 0, 2])
else
(if i.val < 7751 then
[0, 3, 0, 2, 1, 1, 0, 3, 2, 1]
else
[0, 3, 0, 2, 1, 1, 0, 3, 3, 2])))
else
(if i.val < 7756 then
(if i.val < 7754 then
(if i.val < 7753 then
[0, 3, 0, 2, 1, 1, 2, 3, 0, 1]
else
[0, 3, 0, 2, 1, 1, 3, 2, 2, 3])
else
(if i.val < 7755 then
[0, 3, 0, 2, 1, 3, 3, 2, 2, 1]
else
[0, 3, 0, 2, 2, 1, 0, 3, 0, 1]))
else
(if i.val < 7758 then
(if i.val < 7757 then
[0, 3, 0, 2, 2, 1, 3, 3, 0, 1]
else
[0, 3, 0, 2, 2, 3, 0, 1, 2, 3])
else
(if i.val < 7759 then
[0, 3, 0, 2, 3, 3, 0, 1, 1, 2]
else
[0, 3, 0, 2, 3, 3, 0, 2, 1, 3]))))
else
(if i.val < 7768 then
(if i.val < 7764 then
(if i.val < 7762 then
(if i.val < 7761 then
[0, 3, 0, 2, 3, 3, 2, 1, 0, 0]
else
[0, 3, 2, 1, 0, 0, 1, 2, 3, 3])
else
(if i.val < 7763 then
[0, 3, 2, 1, 0, 0, 1, 3, 2, 2]
else
[0, 3, 2, 1, 0, 3, 2, 1, 0, 0]))
else
(if i.val < 7766 then
(if i.val < 7765 then
[0, 3, 2, 1, 0, 3, 2, 2, 1, 0]
else
[0, 3, 2, 1, 0, 3, 2, 2, 1, 3])
else
(if i.val < 7767 then
[0, 3, 2, 1, 0, 3, 3, 2, 1, 0]
else
[0, 3, 2, 1, 1, 0, 0, 2, 3, 0])))
else
(if i.val < 7772 then
(if i.val < 7770 then
(if i.val < 7769 then
[0, 3, 2, 1, 1, 0, 2, 1, 1, 2]
else
[0, 3, 2, 1, 1, 0, 2, 3, 0, 2])
else
(if i.val < 7771 then
[0, 3, 2, 1, 1, 0, 2, 3, 2, 1]
else
[0, 3, 2, 1, 1, 0, 3, 2, 1, 0]))
else
(if i.val < 7774 then
(if i.val < 7773 then
[0, 3, 2, 1, 1, 2, 3, 3, 2, 1]
else
[0, 3, 2, 2, 1, 0, 3, 0, 2, 1])
else
(if i.val < 7775 then
[0, 3, 2, 2, 1, 3, 0, 0, 3, 2]
else
[0, 3, 2, 2, 1, 3, 0, 1, 2, 1])))))
else
(if i.val < 7792 then
(if i.val < 7784 then
(if i.val < 7780 then
(if i.val < 7778 then
(if i.val < 7777 then
[0, 3, 2, 2, 1, 3, 0, 1, 2, 3]
else
[0, 3, 2, 2, 3, 0, 0, 3, 2, 1])
else
(if i.val < 7779 then
[0, 3, 2, 2, 3, 0, 1, 2, 3, 3]
else
[0, 3, 3, 0, 0, 1, 1, 2, 3, 0]))
else
(if i.val < 7782 then
(if i.val < 7781 then
[0, 3, 3, 0, 0, 2, 1, 0, 3, 2]
else
[0, 3, 3, 0, 0, 2, 1, 3, 0, 0])
else
(if i.val < 7783 then
[0, 3, 3, 0, 0, 2, 2, 1, 0, 0]
else
[0, 3, 3, 0, 0, 2, 2, 1, 3, 3])))
else
(if i.val < 7788 then
(if i.val < 7786 then
(if i.val < 7785 then
[0, 3, 3, 0, 0, 2, 3, 3, 2, 1]
else
[0, 3, 3, 0, 1, 1, 0, 2, 2, 1])
else
(if i.val < 7787 then
[0, 3, 3, 0, 1, 1, 2, 3, 3, 2]
else
[0, 3, 3, 0, 1, 2, 1, 0, 3, 0]))
else
(if i.val < 7790 then
(if i.val < 7789 then
[0, 3, 3, 0, 1, 2, 2, 1, 3, 2]
else
[0, 3, 3, 0, 1, 2, 3, 3, 2, 1])
else
(if i.val < 7791 then
[0, 3, 3, 0, 2, 1, 0, 3, 2, 2]
else
[0, 3, 3, 0, 2, 1, 1, 0, 3, 2]))))
else
(if i.val < 7800 then
(if i.val < 7796 then
(if i.val < 7794 then
(if i.val < 7793 then
[0, 3, 3, 0, 2, 1, 1, 3, 2, 2]
else
[0, 3, 3, 0, 2, 1, 3, 3, 2, 1])
else
(if i.val < 7795 then
[0, 3, 3, 0, 2, 2, 1, 3, 3, 2]
else
[0, 3, 3, 0, 2, 3, 3, 2, 1, 1]))
else
(if i.val < 7798 then
(if i.val < 7797 then
[0, 3, 3, 2, 1, 0, 3, 2, 2, 3]
else
[0, 3, 3, 2, 1, 0, 3, 3, 0, 1])
else
(if i.val < 7799 then
[0, 3, 3, 2, 1, 1, 0, 2, 3, 2]
else
[0, 3, 3, 2, 1, 1, 0, 3, 3, 2])))
else
(if i.val < 7804 then
(if i.val < 7802 then
(if i.val < 7801 then
[0, 3, 3, 2, 2, 1, 1, 0, 3, 3]
else
[1, 0, 0, 1, 2, 1, 1, 2, 3, 0])
else
(if i.val < 7803 then
[1, 0, 0, 1, 2, 1, 1, 2, 3, 3]
else
[1, 0, 0, 1, 2, 1, 1, 3, 2, 1]))
else
(if i.val < 7806 then
(if i.val < 7805 then
[1, 0, 0, 1, 2, 1, 1, 3, 3, 2]
else
[1, 0, 0, 1, 2, 1, 3, 3, 2, 2])
else
(if i.val < 7807 then
[1, 0, 0, 1, 2, 2, 1, 0, 3, 3]
else
[1, 0, 0, 1, 2, 2, 1, 3, 0, 2])))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row31_cosetWordsPart0061 : Fin 8640 → List (Fin 4) :=
  fun i => (if i.val < 7872 then
(if i.val < 7840 then
(if i.val < 7824 then
(if i.val < 7816 then
(if i.val < 7812 then
(if i.val < 7810 then
(if i.val < 7809 then
[1, 0, 0, 1, 2, 2, 3, 2, 2, 1]
else
[1, 0, 0, 1, 2, 3, 0, 1, 1, 2])
else
(if i.val < 7811 then
[1, 0, 0, 1, 2, 3, 0, 1, 2, 2]
else
[1, 0, 0, 1, 2, 3, 2, 1, 0, 3]))
else
(if i.val < 7814 then
(if i.val < 7813 then
[1, 0, 0, 1, 2, 3, 3, 0, 1, 2]
else
[1, 0, 0, 1, 2, 3, 3, 0, 2, 2])
else
(if i.val < 7815 then
[1, 0, 0, 1, 3, 0, 0, 1, 1, 2]
else
[1, 0, 0, 1, 3, 0, 0, 3, 2, 1])))
else
(if i.val < 7820 then
(if i.val < 7818 then
(if i.val < 7817 then
[1, 0, 0, 1, 3, 0, 0, 3, 2, 2]
else
[1, 0, 0, 1, 3, 0, 1, 2, 3, 3])
else
(if i.val < 7819 then
[1, 0, 0, 1, 3, 0, 2, 1, 1, 2]
else
[1, 0, 0, 1, 3, 0, 2, 3, 3, 0]))
else
(if i.val < 7822 then
(if i.val < 7821 then
[1, 0, 0, 1, 3, 3, 0, 1, 2, 3]
else
[1, 0, 0, 2, 1, 0, 0, 1, 3, 2])
else
(if i.val < 7823 then
[1, 0, 0, 2, 1, 0, 3, 0, 2, 2]
else
[1, 0, 0, 2, 1, 0, 3, 2, 1, 1]))))
else
(if i.val < 7832 then
(if i.val < 7828 then
(if i.val < 7826 then
(if i.val < 7825 then
[1, 0, 0, 2, 1, 1, 0, 2, 1, 3]
else
[1, 0, 0, 2, 1, 1, 0, 3, 2, 1])
else
(if i.val < 7827 then
[1, 0, 0, 2, 1, 1, 0, 3, 3, 2]
else
[1, 0, 0, 2, 1, 1, 2, 3, 0, 0]))
else
(if i.val < 7830 then
(if i.val < 7829 then
[1, 0, 0, 2, 1, 1, 2, 3, 0, 1]
else
[1, 0, 0, 2, 1, 1, 3, 0, 2, 1])
else
(if i.val < 7831 then
[1, 0, 0, 2, 1, 3, 0, 1, 2, 2]
else
[1, 0, 0, 2, 1, 3, 2, 1, 1, 2])))
else
(if i.val < 7836 then
(if i.val < 7834 then
(if i.val < 7833 then
[1, 0, 0, 2, 1, 3, 3, 0, 1, 2]
else
[1, 0, 0, 2, 2, 1, 0, 3, 2, 1])
else
(if i.val < 7835 then
[1, 0, 0, 2, 2, 1, 1, 0, 3, 2]
else
[1, 0, 0, 2, 2, 1, 3, 0, 1, 1]))
else
(if i.val < 7838 then
(if i.val < 7837 then
[1, 0, 0, 2, 2, 3, 0, 0, 3, 2]
else
[1, 0, 0, 2, 2, 3, 2, 2, 1, 3])
else
(if i.val < 7839 then
[1, 0, 0, 2, 3, 0, 0, 1, 1, 2]
else
[1, 0, 0, 2, 3, 0, 1, 2, 2, 3])))))
else
(if i.val < 7856 then
(if i.val < 7848 then
(if i.val < 7844 then
(if i.val < 7842 then
(if i.val < 7841 then
[1, 0, 0, 2, 3, 0, 2, 2, 1, 3]
else
[1, 0, 0, 2, 3, 0, 2, 2, 3, 0])
else
(if i.val < 7843 then
[1, 0, 0, 2, 3, 2, 2, 1, 1, 0]
else
[1, 0, 0, 2, 3, 2, 2, 1, 1, 3]))
else
(if i.val < 7846 then
(if i.val < 7845 then
[1, 0, 0, 2, 3, 3, 0, 0, 2, 1]
else
[1, 0, 0, 2, 3, 3, 0, 1, 1, 2])
else
(if i.val < 7847 then
[1, 0, 0, 2, 3, 3, 0, 1, 2, 3]
else
[1, 0, 0, 2, 3, 3, 0, 2, 2, 3])))
else
(if i.val < 7852 then
(if i.val < 7850 then
(if i.val < 7849 then
[1, 0, 0, 3, 0, 0, 1, 1, 2, 3]
else
[1, 0, 0, 3, 0, 0, 2, 3, 3, 2])
else
(if i.val < 7851 then
[1, 0, 0, 3, 0, 1, 2, 2, 1, 1]
else
[1, 0, 0, 3, 0, 2, 3, 3, 2, 1]))
else
(if i.val < 7854 then
(if i.val < 7853 then
[1, 0, 0, 3, 2, 1, 0, 3, 2, 1]
else
[1, 0, 0, 3, 2, 1, 1, 2, 3, 0])
else
(if i.val < 7855 then
[1, 0, 0, 3, 2, 2, 1, 1, 3, 2]
else
[1, 0, 0, 3, 3, 0, 0, 2, 3, 3]))))
else
(if i.val < 7864 then
(if i.val < 7860 then
(if i.val < 7858 then
(if i.val < 7857 then
[1, 0, 0, 3, 3, 0, 1, 2, 2, 3]
else
[1, 0, 0, 3, 3, 0, 2, 2, 1, 0])
else
(if i.val < 7859 then
[1, 0, 0, 3, 3, 0, 2, 2, 3, 3]
else
[1, 0, 0, 3, 3, 2, 1, 0, 3, 3]))
else
(if i.val < 7862 then
(if i.val < 7861 then
[1, 0, 0, 3, 3, 2, 1, 1, 0, 0]
else
[1, 0, 2, 1, 0, 0, 1, 2, 3, 0])
else
(if i.val < 7863 then
[1, 0, 2, 1, 0, 0, 1, 2, 3, 3]
else
[1, 0, 2, 1, 0, 3, 0, 0, 1, 2])))
else
(if i.val < 7868 then
(if i.val < 7866 then
(if i.val < 7865 then
[1, 0, 2, 1, 0, 3, 3, 2, 2, 1]
else
[1, 0, 2, 1, 1, 0, 2, 3, 0, 0])
else
(if i.val < 7867 then
[1, 0, 2, 1, 1, 0, 2, 3, 3, 2]
else
[1, 0, 2, 1, 1, 2, 3, 0, 0, 3]))
else
(if i.val < 7870 then
(if i.val < 7869 then
[1, 0, 2, 1, 1, 2, 3, 2, 1, 0]
else
[1, 0, 2, 1, 1, 2, 3, 3, 0, 0])
else
(if i.val < 7871 then
[1, 0, 2, 1, 1, 2, 3, 3, 0, 1]
else
[1, 0, 2, 1, 1, 3, 0, 1, 1, 2]))))))
else
(if i.val < 7904 then
(if i.val < 7888 then
(if i.val < 7880 then
(if i.val < 7876 then
(if i.val < 7874 then
(if i.val < 7873 then
[1, 0, 2, 1, 1, 3, 0, 2, 2, 3]
else
[1, 0, 2, 1, 1, 3, 2, 2, 1, 0])
else
(if i.val < 7875 then
[1, 0, 2, 1, 3, 3, 0, 1, 2, 3]
else
[1, 0, 2, 2, 1, 0, 0, 1, 2, 3]))
else
(if i.val < 7878 then
(if i.val < 7877 then
[1, 0, 2, 2, 1, 1, 0, 3, 2, 1]
else
[1, 0, 2, 2, 1, 1, 3, 2, 1, 0])
else
(if i.val < 7879 then
[1, 0, 2, 2, 1, 1, 3, 2, 2, 3]
else
[1, 0, 2, 2, 1, 3, 3, 2, 1, 0])))
else
(if i.val < 7884 then
(if i.val < 7882 then
(if i.val < 7881 then
[1, 0, 2, 2, 3, 0, 0, 1, 1, 2]
else
[1, 0, 2, 2, 3, 0, 0, 2, 1, 0])
else
(if i.val < 7883 then
[1, 0, 2, 2, 3, 0, 0, 2, 2, 3]
else
[1, 0, 2, 2, 3, 0, 1, 2, 3, 3]))
else
(if i.val < 7886 then
(if i.val < 7885 then
[1, 0, 2, 2, 3, 0, 2, 2, 1, 3]
else
[1, 0, 2, 2, 3, 0, 2, 2, 3, 0])
else
(if i.val < 7887 then
[1, 0, 2, 2, 3, 0, 2, 2, 3, 3]
else
[1, 0, 2, 2, 3, 0, 2, 3, 3, 0]))))
else
(if i.val < 7896 then
(if i.val < 7892 then
(if i.val < 7890 then
(if i.val < 7889 then
[1, 0, 2, 2, 3, 2, 2, 1, 0, 0]
else
[1, 0, 2, 2, 3, 2, 2, 1, 0, 3])
else
(if i.val < 7891 then
[1, 0, 2, 2, 3, 2, 2, 1, 1, 3]
else
[1, 0, 2, 2, 3, 2, 2, 3, 0, 0]))
else
(if i.val < 7894 then
(if i.val < 7893 then
[1, 0, 2, 2, 3, 2, 2, 3, 0, 1]
else
[1, 0, 2, 2, 3, 3, 0, 2, 3, 3])
else
(if i.val < 7895 then
[1, 0, 2, 3, 0, 1, 1, 0, 2, 1]
else
[1, 0, 2, 3, 0, 1, 1, 2, 1, 1])))
else
(if i.val < 7900 then
(if i.val < 7898 then
(if i.val < 7897 then
[1, 0, 2, 3, 0, 1, 2, 3, 3, 2]
else
[1, 0, 2, 3, 0, 2, 1, 1, 3, 2])
else
(if i.val < 7899 then
[1, 0, 2, 3, 3, 0, 0, 2, 1, 3]
else
[1, 0, 2, 3, 3, 0, 1, 1, 0, 2]))
else
(if i.val < 7902 then
(if i.val < 7901 then
[1, 0, 2, 3, 3, 0, 1, 2, 1, 1]
else
[1, 0, 2, 3, 3, 0, 1, 2, 1, 3])
else
(if i.val < 7903 then
[1, 0, 2, 3, 3, 0, 1, 2, 3, 3]
else
[1, 0, 2, 3, 3, 0, 2, 3, 3, 2])))))
else
(if i.val < 7920 then
(if i.val < 7912 then
(if i.val < 7908 then
(if i.val < 7906 then
(if i.val < 7905 then
[1, 0, 2, 3, 3, 2, 1, 0, 0, 3]
else
[1, 0, 3, 0, 0, 1, 1, 2, 1, 3])
else
(if i.val < 7907 then
[1, 0, 3, 0, 0, 1, 1, 2, 2, 1]
else
[1, 0, 3, 0, 0, 1, 1, 2, 2, 3]))
else
(if i.val < 7910 then
(if i.val < 7909 then
[1, 0, 3, 0, 0, 1, 1, 2, 3, 3]
else
[1, 0, 3, 0, 0, 1, 2, 3, 3, 2])
else
(if i.val < 7911 then
[1, 0, 3, 0, 0, 2, 1, 1, 0, 2]
else
[1, 0, 3, 0, 0, 2, 2, 3, 0, 1])))
else
(if i.val < 7916 then
(if i.val < 7914 then
(if i.val < 7913 then
[1, 0, 3, 0, 0, 2, 3, 3, 2, 1]
else
[1, 0, 3, 0, 0, 3, 2, 1, 1, 0])
else
(if i.val < 7915 then
[1, 0, 3, 0, 0, 3, 2, 1, 1, 2]
else
[1, 0, 3, 0, 1, 1, 0, 2, 2, 1]))
else
(if i.val < 7918 then
(if i.val < 7917 then
[1, 0, 3, 0, 1, 1, 0, 2, 3, 3]
else
[1, 0, 3, 0, 1, 2, 3, 3, 0, 2])
else
(if i.val < 7919 then
[1, 0, 3, 0, 1, 2, 3, 3, 2, 1]
else
[1, 0, 3, 0, 2, 1, 1, 2, 3, 0]))))
else
(if i.val < 7928 then
(if i.val < 7924 then
(if i.val < 7922 then
(if i.val < 7921 then
[1, 0, 3, 0, 2, 1, 3, 3, 2, 2]
else
[1, 0, 3, 0, 2, 3, 3, 0, 2, 1])
else
(if i.val < 7923 then
[1, 0, 3, 0, 2, 3, 3, 2, 1, 0]
else
[1, 0, 3, 2, 1, 0, 0, 1, 2, 2]))
else
(if i.val < 7926 then
(if i.val < 7925 then
[1, 0, 3, 2, 1, 1, 0, 2, 3, 2]
else
[1, 0, 3, 2, 1, 1, 2, 3, 0, 1])
else
(if i.val < 7927 then
[1, 0, 3, 2, 2, 1, 0, 0, 1, 3]
else
[1, 0, 3, 2, 2, 1, 0, 3, 2, 1])))
else
(if i.val < 7932 then
(if i.val < 7930 then
(if i.val < 7929 then
[1, 0, 3, 2, 2, 1, 1, 3, 0, 0]
else
[1, 0, 3, 2, 2, 1, 1, 3, 0, 1])
else
(if i.val < 7931 then
[1, 0, 3, 2, 2, 3, 0, 0, 3, 2]
else
[1, 0, 3, 3, 0, 0, 2, 3, 3, 2]))
else
(if i.val < 7934 then
(if i.val < 7933 then
[1, 0, 3, 3, 0, 1, 1, 0, 2, 2]
else
[1, 0, 3, 3, 0, 1, 1, 0, 2, 3])
else
(if i.val < 7935 then
[1, 0, 3, 3, 0, 2, 1, 0, 3, 0]
else
[1, 0, 3, 3, 0, 2, 1, 1, 3, 2])))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row31_cosetWordsPart0062 : Fin 8640 → List (Fin 4) :=
  fun i => (if i.val < 8000 then
(if i.val < 7968 then
(if i.val < 7952 then
(if i.val < 7944 then
(if i.val < 7940 then
(if i.val < 7938 then
(if i.val < 7937 then
[1, 0, 3, 3, 0, 2, 3, 3, 0, 2]
else
[1, 0, 3, 3, 2, 1, 0, 3, 2, 2])
else
(if i.val < 7939 then
[1, 1, 0, 0, 2, 1, 0, 3, 2, 1]
else
[1, 1, 0, 0, 2, 1, 1, 2, 3, 0]))
else
(if i.val < 7942 then
(if i.val < 7941 then
[1, 1, 0, 0, 2, 1, 1, 3, 2, 2]
else
[1, 1, 0, 0, 2, 2, 1, 1, 3, 3])
else
(if i.val < 7943 then
[1, 1, 0, 0, 2, 2, 1, 3, 0, 1]
else
[1, 1, 0, 0, 2, 2, 1, 3, 3, 2])))
else
(if i.val < 7948 then
(if i.val < 7946 then
(if i.val < 7945 then
[1, 1, 0, 0, 2, 2, 3, 2, 2, 1]
else
[1, 1, 0, 0, 2, 2, 3, 2, 2, 3])
else
(if i.val < 7947 then
[1, 1, 0, 0, 2, 3, 2, 1, 0, 3]
else
[1, 1, 0, 0, 2, 3, 3, 2, 1, 0]))
else
(if i.val < 7950 then
(if i.val < 7949 then
[1, 1, 0, 0, 3, 0, 1, 2, 1, 1]
else
[1, 1, 0, 0, 3, 0, 1, 2, 2, 1])
else
(if i.val < 7951 then
[1, 1, 0, 0, 3, 0, 1, 2, 2, 3]
else
[1, 1, 0, 0, 3, 0, 1, 2, 3, 3]))))
else
(if i.val < 7960 then
(if i.val < 7956 then
(if i.val < 7954 then
(if i.val < 7953 then
[1, 1, 0, 2, 1, 0, 0, 1, 3, 2]
else
[1, 1, 0, 2, 1, 0, 3, 3, 2, 2])
else
(if i.val < 7955 then
[1, 1, 0, 2, 1, 1, 0, 0, 2, 3]
else
[1, 1, 0, 2, 1, 1, 0, 2, 1, 3]))
else
(if i.val < 7958 then
(if i.val < 7957 then
[1, 1, 0, 2, 1, 1, 0, 2, 3, 0]
else
[1, 1, 0, 2, 1, 1, 0, 2, 3, 2])
else
(if i.val < 7959 then
[1, 1, 0, 2, 1, 1, 0, 2, 3, 3]
else
[1, 1, 0, 2, 1, 1, 0, 3, 2, 1])))
else
(if i.val < 7964 then
(if i.val < 7962 then
(if i.val < 7961 then
[1, 1, 0, 2, 1, 1, 2, 3, 0, 0]
else
[1, 1, 0, 2, 1, 1, 3, 0, 2, 2])
else
(if i.val < 7963 then
[1, 1, 0, 2, 1, 1, 3, 0, 2, 3]
else
[1, 1, 0, 2, 1, 1, 3, 2, 1, 1]))
else
(if i.val < 7966 then
(if i.val < 7965 then
[1, 1, 0, 2, 1, 3, 3, 2, 2, 1]
else
[1, 1, 0, 2, 2, 1, 1, 0, 3, 2])
else
(if i.val < 7967 then
[1, 1, 0, 2, 2, 1, 1, 3, 0, 1]
else
[1, 1, 0, 2, 2, 3, 2, 2, 1, 3])))))
else
(if i.val < 7984 then
(if i.val < 7976 then
(if i.val < 7972 then
(if i.val < 7970 then
(if i.val < 7969 then
[1, 1, 0, 2, 3, 0, 1, 1, 0, 2]
else
[1, 1, 0, 2, 3, 0, 1, 1, 2, 2])
else
(if i.val < 7971 then
[1, 1, 0, 2, 3, 0, 1, 1, 2, 3]
else
[1, 1, 0, 2, 3, 0, 1, 2, 2, 3]))
else
(if i.val < 7974 then
(if i.val < 7973 then
[1, 1, 0, 2, 3, 0, 2, 1, 3, 3]
else
[1, 1, 0, 2, 3, 2, 1, 1, 0, 0])
else
(if i.val < 7975 then
[1, 1, 0, 2, 3, 3, 0, 2, 1, 1]
else
[1, 1, 0, 2, 3, 3, 0, 2, 3, 3])))
else
(if i.val < 7980 then
(if i.val < 7978 then
(if i.val < 7977 then
[1, 1, 0, 2, 3, 3, 2, 1, 0, 3]
else
[1, 1, 0, 3, 0, 0, 1, 1, 2, 2])
else
(if i.val < 7979 then
[1, 1, 0, 3, 0, 0, 1, 1, 2, 3]
else
[1, 1, 0, 3, 0, 0, 1, 2, 3, 2]))
else
(if i.val < 7982 then
(if i.val < 7981 then
[1, 1, 0, 3, 0, 0, 1, 3, 2, 2]
else
[1, 1, 0, 3, 0, 0, 3, 2, 2, 1])
else
(if i.val < 7983 then
[1, 1, 0, 3, 0, 1, 1, 2, 2, 3]
else
[1, 1, 0, 3, 0, 1, 2, 3, 3, 2]))))
else
(if i.val < 7992 then
(if i.val < 7988 then
(if i.val < 7986 then
(if i.val < 7985 then
[1, 1, 0, 3, 0, 2, 1, 0, 3, 3]
else
[1, 1, 0, 3, 0, 2, 2, 1, 0, 3])
else
(if i.val < 7987 then
[1, 1, 0, 3, 0, 2, 2, 3, 0, 1]
else
[1, 1, 0, 3, 0, 2, 3, 3, 0, 2]))
else
(if i.val < 7990 then
(if i.val < 7989 then
[1, 1, 0, 3, 0, 2, 3, 3, 2, 1]
else
[1, 1, 0, 3, 2, 1, 1, 0, 0, 2])
else
(if i.val < 7991 then
[1, 1, 0, 3, 2, 1, 1, 2, 3, 0]
else
[1, 1, 0, 3, 2, 2, 3, 0, 1, 2])))
else
(if i.val < 7996 then
(if i.val < 7994 then
(if i.val < 7993 then
[1, 1, 0, 3, 3, 0, 1, 2, 1, 1]
else
[1, 1, 0, 3, 3, 0, 1, 2, 2, 1])
else
(if i.val < 7995 then
[1, 1, 0, 3, 3, 0, 2, 3, 3, 2]
else
[1, 1, 2, 1, 0, 3, 0, 1, 2, 3]))
else
(if i.val < 7998 then
(if i.val < 7997 then
[1, 1, 2, 1, 0, 3, 0, 2, 2, 1]
else
[1, 1, 2, 1, 0, 3, 3, 2, 1, 0])
else
(if i.val < 7999 then
[1, 1, 2, 1, 1, 0, 2, 3, 0, 0]
else
[1, 1, 2, 1, 1, 0, 2, 3, 0, 2]))))))
else
(if i.val < 8032 then
(if i.val < 8016 then
(if i.val < 8008 then
(if i.val < 8004 then
(if i.val < 8002 then
(if i.val < 8001 then
[1, 1, 2, 1, 1, 0, 2, 3, 2, 1]
else
[1, 1, 2, 1, 1, 0, 3, 0, 2, 1])
else
(if i.val < 8003 then
[1, 1, 2, 1, 1, 0, 3, 0, 2, 3]
else
[1, 1, 2, 1, 1, 0, 3, 2, 1, 0]))
else
(if i.val < 8006 then
(if i.val < 8005 then
[1, 1, 2, 1, 1, 2, 3, 2, 1, 1]
else
[1, 1, 2, 1, 1, 2, 3, 2, 2, 1])
else
(if i.val < 8007 then
[1, 1, 2, 1, 1, 2, 3, 3, 0, 1]
else
[1, 1, 2, 1, 3, 0, 0, 1, 2, 3])))
else
(if i.val < 8012 then
(if i.val < 8010 then
(if i.val < 8009 then
[1, 1, 2, 1, 3, 3, 2, 2, 1, 1]
else
[1, 1, 2, 2, 1, 0, 3, 2, 1, 0])
else
(if i.val < 8011 then
[1, 1, 2, 2, 1, 1, 0, 3, 2, 1]
else
[1, 1, 2, 2, 1, 1, 0, 3, 3, 2]))
else
(if i.val < 8014 then
(if i.val < 8013 then
[1, 1, 2, 2, 1, 1, 3, 2, 1, 1]
else
[1, 1, 2, 2, 1, 3, 0, 0, 3, 2])
else
(if i.val < 8015 then
[1, 1, 2, 2, 3, 0, 0, 1, 1, 2]
else
[1, 1, 2, 2, 3, 0, 0, 3, 2, 1]))))
else
(if i.val < 8024 then
(if i.val < 8020 then
(if i.val < 8018 then
(if i.val < 8017 then
[1, 1, 2, 2, 3, 0, 1, 2, 3, 0]
else
[1, 1, 2, 2, 3, 0, 1, 2, 3, 3])
else
(if i.val < 8019 then
[1, 1, 2, 3, 0, 1, 1, 2, 1, 0]
else
[1, 1, 2, 3, 0, 1, 1, 2, 1, 1]))
else
(if i.val < 8022 then
(if i.val < 8021 then
[1, 1, 2, 3, 0, 1, 1, 2, 3, 3]
else
[1, 1, 2, 3, 0, 1, 2, 1, 3, 2])
else
(if i.val < 8023 then
[1, 1, 2, 3, 0, 1, 2, 2, 1, 0]
else
[1, 1, 2, 3, 0, 1, 2, 2, 1, 3])))
else
(if i.val < 8028 then
(if i.val < 8026 then
(if i.val < 8025 then
[1, 1, 2, 3, 0, 1, 2, 2, 3, 0]
else
[1, 1, 2, 3, 2, 2, 1, 3, 2, 2])
else
(if i.val < 8027 then
[1, 1, 2, 3, 3, 0, 1, 2, 1, 1]
else
[1, 1, 2, 3, 3, 0, 2, 3, 3, 2]))
else
(if i.val < 8030 then
(if i.val < 8029 then
[1, 1, 2, 3, 3, 2, 1, 0, 0, 3]
else
[1, 1, 3, 0, 0, 1, 1, 2, 1, 3])
else
(if i.val < 8031 then
[1, 1, 3, 0, 0, 1, 1, 2, 2, 1]
else
[1, 1, 3, 0, 0, 1, 1, 2, 2, 3])))))
else
(if i.val < 8048 then
(if i.val < 8040 then
(if i.val < 8036 then
(if i.val < 8034 then
(if i.val < 8033 then
[1, 1, 3, 0, 0, 1, 1, 2, 3, 0]
else
[1, 1, 3, 0, 0, 1, 1, 2, 3, 3])
else
(if i.val < 8035 then
[1, 1, 3, 0, 0, 1, 2, 3, 3, 2]
else
[1, 1, 3, 0, 0, 2, 1, 0, 3, 2]))
else
(if i.val < 8038 then
(if i.val < 8037 then
[1, 1, 3, 0, 0, 3, 2, 1, 1, 0]
else
[1, 1, 3, 0, 0, 3, 2, 2, 3, 0])
else
(if i.val < 8039 then
[1, 1, 3, 0, 1, 2, 1, 1, 0, 3]
else
[1, 1, 3, 0, 2, 1, 1, 2, 3, 2])))
else
(if i.val < 8044 then
(if i.val < 8042 then
(if i.val < 8041 then
[1, 1, 3, 0, 2, 1, 1, 3, 2, 2]
else
[1, 1, 3, 0, 2, 1, 3, 3, 0, 2])
else
(if i.val < 8043 then
[1, 1, 3, 0, 2, 1, 3, 3, 2, 1]
else
[1, 1, 3, 0, 2, 2, 1, 3, 3, 2]))
else
(if i.val < 8046 then
(if i.val < 8045 then
[1, 1, 3, 0, 2, 3, 3, 0, 2, 1]
else
[1, 1, 3, 0, 2, 3, 3, 2, 1, 1])
else
(if i.val < 8047 then
[1, 1, 3, 2, 2, 1, 0, 3, 2, 1]
else
[1, 1, 3, 2, 2, 1, 1, 3, 0, 1]))))
else
(if i.val < 8056 then
(if i.val < 8052 then
(if i.val < 8050 then
(if i.val < 8049 then
[1, 1, 3, 3, 0, 1, 2, 3, 0, 1]
else
[1, 1, 3, 3, 0, 2, 1, 1, 3, 2])
else
(if i.val < 8051 then
[1, 1, 3, 3, 0, 2, 3, 3, 0, 2]
else
[1, 1, 3, 3, 2, 1, 0, 3, 2, 2]))
else
(if i.val < 8054 then
(if i.val < 8053 then
[1, 2, 1, 0, 0, 1, 3, 0, 2, 2]
else
[1, 2, 1, 0, 0, 1, 3, 2, 2, 3])
else
(if i.val < 8055 then
[1, 2, 1, 0, 0, 1, 3, 3, 0, 2]
else
[1, 2, 1, 0, 3, 0, 1, 1, 0, 2])))
else
(if i.val < 8060 then
(if i.val < 8058 then
(if i.val < 8057 then
[1, 2, 1, 0, 3, 0, 1, 1, 2, 1]
else
[1, 2, 1, 0, 3, 2, 2, 3, 0, 1])
else
(if i.val < 8059 then
[1, 2, 1, 0, 3, 3, 0, 0, 2, 1]
else
[1, 2, 1, 0, 3, 3, 0, 1, 2, 1]))
else
(if i.val < 8062 then
(if i.val < 8061 then
[1, 2, 1, 0, 3, 3, 0, 2, 3, 3]
else
[1, 2, 1, 1, 0, 0, 3, 2, 2, 1])
else
(if i.val < 8063 then
[1, 2, 1, 1, 0, 0, 3, 3, 2, 2]
else
[1, 2, 1, 1, 0, 2, 1, 3, 0, 0])))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row31_cosetWordsPart0063 : Fin 8640 → List (Fin 4) :=
  fun i => (if i.val < 8128 then
(if i.val < 8096 then
(if i.val < 8080 then
(if i.val < 8072 then
(if i.val < 8068 then
(if i.val < 8066 then
(if i.val < 8065 then
[1, 2, 1, 1, 0, 2, 1, 3, 0, 1]
else
[1, 2, 1, 1, 0, 2, 3, 0, 2, 1])
else
(if i.val < 8067 then
[1, 2, 1, 1, 0, 3, 0, 1, 1, 2]
else
[1, 2, 1, 1, 0, 3, 0, 1, 2, 1]))
else
(if i.val < 8070 then
(if i.val < 8069 then
[1, 2, 1, 1, 0, 3, 0, 2, 1, 3]
else
[1, 2, 1, 1, 0, 3, 2, 1, 1, 0])
else
(if i.val < 8071 then
[1, 2, 1, 1, 3, 0, 0, 1, 2, 1]
else
[1, 2, 1, 1, 3, 0, 0, 3, 2, 2])))
else
(if i.val < 8076 then
(if i.val < 8074 then
(if i.val < 8073 then
[1, 2, 1, 1, 3, 0, 1, 2, 2, 1]
else
[1, 2, 1, 1, 3, 0, 1, 2, 2, 3])
else
(if i.val < 8075 then
[1, 2, 1, 1, 3, 0, 2, 1, 1, 2]
else
[1, 2, 1, 1, 3, 0, 2, 3, 3, 2]))
else
(if i.val < 8078 then
(if i.val < 8077 then
[1, 2, 1, 1, 3, 2, 2, 1, 1, 3]
else
[1, 2, 1, 3, 0, 0, 3, 2, 2, 1])
else
(if i.val < 8079 then
[1, 2, 1, 3, 0, 1, 2, 2, 1, 0]
else
[1, 2, 1, 3, 0, 1, 2, 2, 1, 1]))))
else
(if i.val < 8088 then
(if i.val < 8084 then
(if i.val < 8082 then
(if i.val < 8081 then
[1, 2, 1, 3, 0, 1, 2, 2, 1, 3]
else
[1, 2, 1, 3, 0, 1, 2, 2, 3, 0])
else
(if i.val < 8083 then
[1, 2, 1, 3, 0, 2, 3, 3, 2, 1]
else
[1, 2, 1, 3, 2, 1, 0, 3, 3, 2]))
else
(if i.val < 8086 then
(if i.val < 8085 then
[1, 2, 1, 3, 3, 0, 0, 2, 2, 3]
else
[1, 2, 1, 3, 3, 0, 1, 2, 1, 1])
else
(if i.val < 8087 then
[1, 2, 1, 3, 3, 0, 1, 2, 2, 3]
else
[1, 2, 1, 3, 3, 0, 2, 2, 1, 0])))
else
(if i.val < 8092 then
(if i.val < 8090 then
(if i.val < 8089 then
[1, 2, 1, 3, 3, 0, 2, 2, 1, 3]
else
[1, 2, 2, 1, 0, 0, 1, 2, 3, 3])
else
(if i.val < 8091 then
[1, 2, 2, 1, 0, 3, 0, 2, 1, 0]
else
[1, 2, 2, 1, 0, 3, 0, 2, 3, 3]))
else
(if i.val < 8094 then
(if i.val < 8093 then
[1, 2, 2, 1, 1, 0, 0, 3, 3, 2]
else
[1, 2, 2, 1, 1, 0, 3, 0, 2, 1])
else
(if i.val < 8095 then
[1, 2, 2, 1, 1, 0, 3, 0, 2, 3]
else
[1, 2, 2, 1, 1, 0, 3, 2, 1, 1])))))
else
(if i.val < 8112 then
(if i.val < 8104 then
(if i.val < 8100 then
(if i.val < 8098 then
(if i.val < 8097 then
[1, 2, 2, 1, 1, 3, 0, 2, 1, 0]
else
[1, 2, 2, 1, 3, 0, 0, 1, 2, 3])
else
(if i.val < 8099 then
[1, 2, 2, 1, 3, 0, 2, 1, 1, 2]
else
[1, 2, 2, 1, 3, 3, 0, 0, 1, 2]))
else
(if i.val < 8102 then
(if i.val < 8101 then
[1, 2, 2, 1, 3, 3, 2, 1, 0, 3]
else
[1, 2, 2, 3, 0, 0, 1, 1, 2, 2])
else
(if i.val < 8103 then
[1, 2, 2, 3, 0, 0, 1, 2, 2, 1]
else
[1, 2, 2, 3, 0, 0, 1, 2, 2, 3])))
else
(if i.val < 8108 then
(if i.val < 8106 then
(if i.val < 8105 then
[1, 2, 2, 3, 0, 1, 2, 3, 0, 1]
else
[1, 2, 2, 3, 0, 2, 2, 1, 0, 3])
else
(if i.val < 8107 then
[1, 2, 2, 3, 0, 2, 3, 3, 2, 1]
else
[1, 2, 3, 0, 0, 1, 1, 2, 1, 1]))
else
(if i.val < 8110 then
(if i.val < 8109 then
[1, 2, 3, 0, 0, 3, 2, 2, 1, 3]
else
[1, 2, 3, 0, 0, 3, 2, 2, 3, 0])
else
(if i.val < 8111 then
[1, 2, 3, 0, 1, 1, 0, 2, 3, 2]
else
[1, 2, 3, 0, 1, 1, 0, 3, 2, 1]))))
else
(if i.val < 8120 then
(if i.val < 8116 then
(if i.val < 8114 then
(if i.val < 8113 then
[1, 2, 3, 0, 1, 2, 1, 1, 0, 3]
else
[1, 2, 3, 0, 1, 2, 2, 1, 0, 0])
else
(if i.val < 8115 then
[1, 2, 3, 0, 1, 2, 2, 1, 3, 3]
else
[1, 2, 3, 0, 1, 2, 2, 3, 0, 0]))
else
(if i.val < 8118 then
(if i.val < 8117 then
[1, 2, 3, 0, 1, 2, 2, 3, 3, 0]
else
[1, 2, 3, 0, 2, 1, 1, 3, 2, 2])
else
(if i.val < 8119 then
[1, 2, 3, 0, 2, 2, 1, 3, 3, 2]
else
[1, 2, 3, 2, 1, 0, 0, 3, 2, 2])))
else
(if i.val < 8124 then
(if i.val < 8122 then
(if i.val < 8121 then
[1, 2, 3, 2, 2, 1, 0, 3, 2, 2]
else
[1, 2, 3, 3, 0, 0, 1, 1, 2, 2])
else
(if i.val < 8123 then
[1, 2, 3, 3, 0, 1, 1, 0, 2, 2]
else
[1, 2, 3, 3, 0, 1, 2, 1, 0, 0]))
else
(if i.val < 8126 then
(if i.val < 8125 then
[1, 2, 3, 3, 0, 1, 2, 1, 1, 0]
else
[1, 2, 3, 3, 0, 1, 2, 1, 1, 3])
else
(if i.val < 8127 then
[1, 2, 3, 3, 0, 1, 2, 1, 3, 3]
else
[1, 2, 3, 3, 0, 1, 2, 2, 1, 0]))))))
else
(if i.val < 8160 then
(if i.val < 8144 then
(if i.val < 8136 then
(if i.val < 8132 then
(if i.val < 8130 then
(if i.val < 8129 then
[1, 2, 3, 3, 0, 1, 2, 3, 0, 0]
else
[1, 2, 3, 3, 0, 2, 1, 1, 3, 2])
else
(if i.val < 8131 then
[1, 2, 3, 3, 2, 1, 0, 0, 1, 3]
else
[1, 3, 0, 0, 1, 1, 2, 1, 0, 0]))
else
(if i.val < 8134 then
(if i.val < 8133 then
[1, 3, 0, 0, 1, 1, 2, 2, 1, 0]
else
[1, 3, 0, 0, 1, 1, 2, 2, 1, 1])
else
(if i.val < 8135 then
[1, 3, 0, 0, 1, 1, 2, 2, 1, 3]
else
[1, 3, 0, 0, 1, 1, 2, 3, 3, 2])))
else
(if i.val < 8140 then
(if i.val < 8138 then
(if i.val < 8137 then
[1, 3, 0, 0, 1, 2, 1, 1, 2, 3]
else
[1, 3, 0, 0, 1, 2, 2, 3, 0, 1])
else
(if i.val < 8139 then
[1, 3, 0, 0, 1, 3, 2, 1, 1, 2]
else
[1, 3, 0, 0, 2, 1, 0, 3, 2, 2]))
else
(if i.val < 8142 then
(if i.val < 8141 then
[1, 3, 0, 0, 2, 1, 1, 2, 3, 2]
else
[1, 3, 0, 0, 2, 1, 1, 2, 3, 3])
else
(if i.val < 8143 then
[1, 3, 0, 0, 2, 1, 1, 3, 2, 2]
else
[1, 3, 0, 0, 2, 2, 1, 1, 3, 2]))))
else
(if i.val < 8152 then
(if i.val < 8148 then
(if i.val < 8146 then
(if i.val < 8145 then
[1, 3, 0, 0, 2, 2, 1, 3, 3, 2]
else
[1, 3, 0, 0, 2, 2, 3, 0, 2, 2])
else
(if i.val < 8147 then
[1, 3, 0, 0, 2, 2, 3, 2, 2, 1]
else
[1, 3, 0, 0, 2, 3, 2, 1, 1, 2]))
else
(if i.val < 8150 then
(if i.val < 8149 then
[1, 3, 0, 0, 3, 2, 1, 1, 0, 2]
else
[1, 3, 0, 0, 3, 2, 2, 1, 1, 3])
else
(if i.val < 8151 then
[1, 3, 0, 0, 3, 2, 2, 3, 0, 0]
else
[1, 3, 0, 1, 1, 0, 2, 1, 1, 2])))
else
(if i.val < 8156 then
(if i.val < 8154 then
(if i.val < 8153 then
[1, 3, 0, 1, 1, 0, 3, 3, 0, 2]
else
[1, 3, 0, 1, 1, 2, 2, 3, 3, 0])
else
(if i.val < 8155 then
[1, 3, 0, 1, 2, 1, 0, 3, 0, 1]
else
[1, 3, 0, 1, 2, 1, 1, 0, 2, 3]))
else
(if i.val < 8158 then
(if i.val < 8157 then
[1, 3, 0, 1, 2, 1, 3, 2, 2, 1]
else
[1, 3, 0, 1, 2, 1, 3, 3, 2, 1])
else
(if i.val < 8159 then
[1, 3, 0, 1, 2, 1, 3, 3, 2, 2]
else
[1, 3, 0, 2, 1, 1, 0, 0, 2, 1])))))
else
(if i.val < 8176 then
(if i.val < 8168 then
(if i.val < 8164 then
(if i.val < 8162 then
(if i.val < 8161 then
[1, 3, 0, 2, 1, 1, 0, 0, 2, 3]
else
[1, 3, 0, 2, 1, 1, 3, 2, 2, 3])
else
(if i.val < 8163 then
[1, 3, 0, 2, 1, 3, 3, 0, 2, 2]
else
[1, 3, 0, 2, 1, 3, 3, 2, 2, 1]))
else
(if i.val < 8166 then
(if i.val < 8165 then
[1, 3, 0, 2, 2, 3, 0, 1, 2, 3]
else
[1, 3, 0, 2, 3, 3, 0, 2, 1, 1])
else
(if i.val < 8167 then
[1, 3, 2, 1, 0, 0, 3, 2, 2, 1]
else
[1, 3, 2, 1, 0, 3, 3, 0, 2, 2])))
else
(if i.val < 8172 then
(if i.val < 8170 then
(if i.val < 8169 then
[1, 3, 2, 2, 1, 0, 0, 1, 2, 3]
else
[1, 3, 2, 2, 1, 1, 3, 0, 2, 1])
else
(if i.val < 8171 then
[1, 3, 2, 2, 1, 3, 0, 0, 1, 2]
else
[1, 3, 2, 2, 1, 3, 0, 0, 3, 2]))
else
(if i.val < 8174 then
(if i.val < 8173 then
[1, 3, 3, 0, 0, 1, 2, 3, 3, 2]
else
[1, 3, 3, 0, 0, 2, 1, 1, 2, 3])
else
(if i.val < 8175 then
[1, 3, 3, 0, 0, 2, 3, 3, 2, 1]
else
[1, 3, 3, 0, 1, 1, 2, 2, 1, 1]))))
else
(if i.val < 8184 then
(if i.val < 8180 then
(if i.val < 8178 then
(if i.val < 8177 then
[1, 3, 3, 0, 1, 2, 1, 1, 0, 2]
else
[1, 3, 3, 0, 1, 2, 1, 1, 3, 3])
else
(if i.val < 8179 then
[1, 3, 3, 0, 2, 1, 0, 3, 2, 2]
else
[1, 3, 3, 0, 2, 1, 1, 0, 2, 1]))
else
(if i.val < 8182 then
(if i.val < 8181 then
[1, 3, 3, 0, 2, 1, 1, 0, 2, 3]
else
[1, 3, 3, 2, 1, 1, 0, 0, 2, 3])
else
(if i.val < 8183 then
[2, 1, 0, 0, 1, 3, 0, 1, 2, 1]
else
[2, 1, 0, 0, 3, 3, 0, 1, 2, 3])))
else
(if i.val < 8188 then
(if i.val < 8186 then
(if i.val < 8185 then
[2, 1, 0, 3, 0, 0, 2, 1, 3, 3]
else
[2, 1, 0, 3, 0, 0, 3, 2, 1, 0])
else
(if i.val < 8187 then
[2, 1, 0, 3, 0, 1, 1, 2, 1, 1]
else
[2, 1, 0, 3, 0, 2, 2, 1, 0, 3]))
else
(if i.val < 8190 then
(if i.val < 8189 then
[2, 1, 0, 3, 2, 2, 3, 0, 0, 3]
else
[2, 1, 0, 3, 3, 0, 0, 2, 3, 3])
else
(if i.val < 8191 then
[2, 1, 0, 3, 3, 0, 1, 2, 1, 1]
else
[2, 1, 0, 3, 3, 0, 1, 2, 3, 3])))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row31_cosetWordsPart0064 : Fin 8640 → List (Fin 4) :=
  fun i => (if i.val < 8256 then
(if i.val < 8224 then
(if i.val < 8208 then
(if i.val < 8200 then
(if i.val < 8196 then
(if i.val < 8194 then
(if i.val < 8193 then
[2, 1, 0, 3, 3, 0, 2, 1, 0, 0]
else
[2, 1, 0, 3, 3, 0, 2, 3, 3, 2])
else
(if i.val < 8195 then
[2, 1, 1, 0, 0, 2, 3, 3, 2, 1]
else
[2, 1, 1, 0, 0, 3, 3, 0, 2, 2]))
else
(if i.val < 8198 then
(if i.val < 8197 then
[2, 1, 1, 0, 2, 3, 0, 2, 1, 0]
else
[2, 1, 1, 0, 2, 3, 0, 2, 1, 1])
else
(if i.val < 8199 then
[2, 1, 1, 0, 2, 3, 0, 2, 1, 3]
else
[2, 1, 1, 0, 2, 3, 2, 1, 0, 0])))
else
(if i.val < 8204 then
(if i.val < 8202 then
(if i.val < 8201 then
[2, 1, 1, 0, 3, 0, 1, 1, 2, 2]
else
[2, 1, 1, 0, 3, 0, 2, 1, 0, 0])
else
(if i.val < 8203 then
[2, 1, 1, 0, 3, 0, 2, 1, 0, 3]
else
[2, 1, 1, 0, 3, 2, 1, 1, 0, 0]))
else
(if i.val < 8206 then
(if i.val < 8205 then
[2, 1, 1, 0, 3, 2, 1, 1, 2, 3]
else
[2, 1, 1, 2, 3, 0, 1, 2, 2, 1])
else
(if i.val < 8207 then
[2, 1, 1, 3, 0, 0, 1, 2, 3, 3]
else
[2, 1, 1, 3, 0, 0, 2, 1, 1, 2]))))
else
(if i.val < 8216 then
(if i.val < 8212 then
(if i.val < 8210 then
(if i.val < 8209 then
[2, 1, 1, 3, 0, 1, 1, 2, 1, 0]
else
[2, 1, 1, 3, 0, 1, 2, 2, 1, 3])
else
(if i.val < 8211 then
[2, 1, 1, 3, 0, 2, 3, 3, 2, 1]
else
[2, 1, 1, 3, 2, 1, 0, 3, 3, 2]))
else
(if i.val < 8214 then
(if i.val < 8213 then
[2, 1, 1, 3, 2, 2, 1, 0, 3, 2]
else
[2, 1, 1, 3, 2, 2, 3, 0, 1, 1])
else
(if i.val < 8215 then
[2, 1, 1, 3, 3, 0, 1, 2, 1, 0]
else
[2, 1, 1, 3, 3, 0, 1, 2, 1, 1])))
else
(if i.val < 8220 then
(if i.val < 8218 then
(if i.val < 8217 then
[2, 1, 1, 3, 3, 0, 1, 2, 1, 3]
else
[2, 1, 1, 3, 3, 0, 2, 3, 3, 2])
else
(if i.val < 8219 then
[2, 1, 3, 0, 0, 1, 2, 1, 1, 2]
else
[2, 1, 3, 0, 0, 1, 2, 2, 1, 1]))
else
(if i.val < 8222 then
(if i.val < 8221 then
[2, 1, 3, 0, 0, 1, 2, 2, 3, 0]
else
[2, 1, 3, 0, 0, 2, 1, 1, 2, 3])
else
(if i.val < 8223 then
[2, 1, 3, 0, 0, 2, 3, 3, 2, 1]
else
[2, 1, 3, 0, 1, 2, 2, 3, 0, 0])))))
else
(if i.val < 8240 then
(if i.val < 8232 then
(if i.val < 8228 then
(if i.val < 8226 then
(if i.val < 8225 then
[2, 1, 3, 3, 0, 0, 1, 2, 2, 3]
else
[2, 1, 3, 3, 0, 0, 2, 3, 3, 2])
else
(if i.val < 8227 then
[2, 1, 3, 3, 0, 1, 2, 2, 1, 1]
else
[2, 2, 1, 0, 3, 0, 2, 1, 0, 3]))
else
(if i.val < 8230 then
(if i.val < 8229 then
[2, 2, 1, 0, 3, 0, 2, 1, 1, 0]
else
[2, 2, 1, 0, 3, 0, 2, 3, 3, 0])
else
(if i.val < 8231 then
[2, 2, 1, 0, 3, 3, 0, 1, 2, 3]
else
[2, 2, 1, 1, 0, 0, 3, 2, 2, 1])))
else
(if i.val < 8236 then
(if i.val < 8234 then
(if i.val < 8233 then
[2, 2, 1, 1, 0, 3, 0, 0, 2, 3]
else
[2, 2, 1, 1, 0, 3, 0, 2, 1, 0])
else
(if i.val < 8235 then
[2, 2, 1, 1, 0, 3, 2, 1, 0, 0]
else
[2, 2, 1, 1, 0, 3, 3, 0, 1, 2]))
else
(if i.val < 8238 then
(if i.val < 8237 then
[2, 2, 1, 1, 3, 3, 0, 1, 2, 1]
else
[2, 2, 1, 3, 0, 0, 1, 2, 1, 1])
else
(if i.val < 8239 then
[2, 2, 1, 3, 0, 1, 2, 1, 1, 2]
else
[2, 2, 1, 3, 0, 2, 3, 3, 0, 2]))))
else
(if i.val < 8248 then
(if i.val < 8244 then
(if i.val < 8242 then
(if i.val < 8241 then
[2, 2, 1, 3, 3, 0, 1, 2, 1, 0]
else
[2, 2, 1, 3, 3, 0, 1, 2, 1, 1])
else
(if i.val < 8243 then
[2, 2, 3, 0, 1, 1, 0, 2, 3, 2]
else
[2, 2, 3, 0, 1, 1, 0, 3, 2, 1]))
else
(if i.val < 8246 then
(if i.val < 8245 then
[2, 2, 3, 0, 1, 2, 1, 1, 0, 3]
else
[2, 2, 3, 0, 1, 2, 1, 1, 2, 3])
else
(if i.val < 8247 then
[2, 2, 3, 0, 1, 2, 1, 1, 3, 3]
else
[2, 2, 3, 0, 2, 3, 3, 2, 1, 1])))
else
(if i.val < 8252 then
(if i.val < 8250 then
(if i.val < 8249 then
[2, 2, 3, 2, 1, 0, 0, 1, 2, 2]
else
[2, 2, 3, 2, 1, 0, 3, 2, 2, 1])
else
(if i.val < 8251 then
[2, 2, 3, 2, 2, 1, 0, 3, 2, 1]
else
[2, 2, 3, 2, 2, 1, 3, 0, 1, 2]))
else
(if i.val < 8254 then
(if i.val < 8253 then
[2, 2, 3, 2, 2, 3, 0, 0, 3, 2]
else
[2, 2, 3, 2, 2, 3, 0, 1, 2, 3])
else
(if i.val < 8255 then
[2, 2, 3, 3, 0, 1, 1, 0, 3, 2]
else
[2, 2, 3, 3, 0, 1, 2, 1, 1, 0]))))))
else
(if i.val < 8288 then
(if i.val < 8272 then
(if i.val < 8264 then
(if i.val < 8260 then
(if i.val < 8258 then
(if i.val < 8257 then
[2, 2, 3, 3, 0, 2, 2, 1, 1, 3]
else
[2, 2, 3, 3, 0, 2, 3, 3, 2, 1])
else
(if i.val < 8259 then
[2, 3, 0, 0, 1, 2, 2, 3, 0, 0]
else
[2, 3, 0, 0, 2, 2, 1, 3, 3, 2]))
else
(if i.val < 8262 then
(if i.val < 8261 then
[2, 3, 0, 0, 2, 3, 2, 1, 0, 0]
else
[2, 3, 0, 0, 2, 3, 3, 2, 1, 0])
else
(if i.val < 8263 then
[2, 3, 0, 1, 1, 0, 2, 1, 0, 0]
else
[2, 3, 0, 1, 1, 0, 2, 1, 1, 2])))
else
(if i.val < 8268 then
(if i.val < 8266 then
(if i.val < 8265 then
[2, 3, 0, 1, 1, 0, 3, 2, 1, 1]
else
[2, 3, 0, 1, 1, 2, 3, 3, 0, 1])
else
(if i.val < 8267 then
[2, 3, 0, 1, 2, 1, 1, 0, 2, 3]
else
[2, 3, 0, 1, 2, 1, 3, 3, 2, 2]))
else
(if i.val < 8270 then
(if i.val < 8269 then
[2, 3, 0, 1, 2, 2, 3, 3, 0, 0]
else
[2, 3, 0, 2, 1, 1, 0, 0, 2, 1])
else
(if i.val < 8271 then
[2, 3, 0, 2, 1, 1, 0, 3, 0, 2]
else
[2, 3, 0, 2, 1, 1, 2, 3, 3, 0]))))
else
(if i.val < 8280 then
(if i.val < 8276 then
(if i.val < 8274 then
(if i.val < 8273 then
[2, 3, 0, 2, 1, 1, 3, 2, 2, 3]
else
[2, 3, 0, 2, 1, 3, 3, 0, 2, 2])
else
(if i.val < 8275 then
[2, 3, 0, 2, 1, 3, 3, 2, 2, 1]
else
[2, 3, 2, 1, 0, 0, 3, 2, 2, 1]))
else
(if i.val < 8278 then
(if i.val < 8277 then
[2, 3, 2, 1, 1, 0, 2, 3, 2, 1]
else
[2, 3, 2, 1, 1, 0, 2, 3, 3, 2])
else
(if i.val < 8279 then
[2, 3, 2, 2, 1, 0, 0, 3, 2, 2]
else
[2, 3, 2, 2, 1, 3, 0, 1, 2, 3])))
else
(if i.val < 8284 then
(if i.val < 8282 then
(if i.val < 8281 then
[2, 3, 3, 0, 0, 2, 1, 1, 2, 3]
else
[2, 3, 3, 0, 1, 1, 0, 2, 2, 1])
else
(if i.val < 8283 then
[2, 3, 3, 0, 1, 2, 1, 3, 3, 0]
else
[2, 3, 3, 0, 2, 3, 3, 2, 1, 1]))
else
(if i.val < 8286 then
(if i.val < 8285 then
[2, 3, 3, 2, 1, 0, 3, 2, 2, 1]
else
[2, 3, 3, 2, 1, 1, 0, 3, 3, 2])
else
(if i.val < 8287 then
[2, 3, 3, 2, 2, 1, 0, 0, 1, 2]
else
[3, 0, 0, 1, 1, 2, 1, 0, 3, 2])))))
else
(if i.val < 8304 then
(if i.val < 8296 then
(if i.val < 8292 then
(if i.val < 8290 then
(if i.val < 8289 then
[3, 0, 0, 1, 1, 2, 1, 1, 0, 0]
else
[3, 0, 0, 1, 1, 2, 1, 3, 3, 0])
else
(if i.val < 8291 then
[3, 0, 0, 1, 1, 2, 2, 3, 0, 1]
else
[3, 0, 0, 1, 1, 2, 2, 3, 3, 0]))
else
(if i.val < 8294 then
(if i.val < 8293 then
[3, 0, 0, 1, 1, 2, 3, 3, 2, 1]
else
[3, 0, 0, 1, 2, 1, 1, 3, 2, 2])
else
(if i.val < 8295 then
[3, 0, 0, 1, 2, 2, 1, 1, 3, 0]
else
[3, 0, 0, 1, 2, 2, 3, 0, 0, 3])))
else
(if i.val < 8300 then
(if i.val < 8298 then
(if i.val < 8297 then
[3, 0, 0, 1, 2, 3, 3, 2, 1, 1]
else
[3, 0, 0, 2, 2, 1, 0, 3, 2, 1])
else
(if i.val < 8299 then
[3, 0, 0, 2, 3, 2, 1, 1, 2, 3]
else
[3, 0, 0, 2, 3, 3, 2, 1, 0, 0]))
else
(if i.val < 8302 then
(if i.val < 8301 then
[3, 0, 0, 3, 2, 1, 0, 3, 2, 2]
else
[3, 0, 0, 3, 2, 2, 3, 0, 1, 2])
else
(if i.val < 8303 then
[3, 0, 1, 1, 0, 2, 1, 1, 2, 3]
else
[3, 0, 1, 1, 0, 3, 2, 1, 1, 2]))))
else
(if i.val < 8312 then
(if i.val < 8308 then
(if i.val < 8306 then
(if i.val < 8305 then
[3, 0, 1, 1, 2, 1, 1, 0, 2, 1]
else
[3, 0, 1, 1, 2, 1, 1, 2, 3, 3])
else
(if i.val < 8307 then
[3, 0, 1, 2, 1, 3, 3, 0, 1, 2]
else
[3, 0, 1, 2, 2, 1, 3, 0, 1, 2]))
else
(if i.val < 8310 then
(if i.val < 8309 then
[3, 0, 1, 2, 3, 3, 0, 1, 2, 1]
else
[3, 0, 1, 2, 3, 3, 2, 1, 0, 0])
else
(if i.val < 8311 then
[3, 0, 2, 1, 0, 0, 1, 2, 2, 3]
else
[3, 0, 2, 1, 0, 3, 3, 2, 1, 1])))
else
(if i.val < 8316 then
(if i.val < 8314 then
(if i.val < 8313 then
[3, 0, 2, 1, 1, 0, 0, 2, 1, 3]
else
[3, 0, 2, 1, 1, 0, 2, 1, 1, 2])
else
(if i.val < 8315 then
[3, 0, 2, 1, 1, 0, 2, 3, 0, 0]
else
[3, 0, 2, 1, 1, 2, 3, 3, 0, 0]))
else
(if i.val < 8318 then
(if i.val < 8317 then
[3, 0, 2, 1, 1, 2, 3, 3, 0, 1]
else
[3, 0, 2, 1, 3, 3, 0, 2, 2, 3])
else
(if i.val < 8319 then
[3, 0, 2, 1, 3, 3, 2, 1, 0, 0]
else
[3, 0, 2, 2, 1, 0, 0, 1, 3, 2])))))))

end HodgeLean.Foundations.Program

end
