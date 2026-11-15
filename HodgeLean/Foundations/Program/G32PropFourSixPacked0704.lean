import HodgeLean.Foundations.Program.HurwitzPrymRexG32Core
import HodgeLean.Foundations.Program.G32PropFourSixPacked0701
import HodgeLean.Foundations.Program.G32PropFourSixPacked0702
import HodgeLean.Foundations.Program.G32PropFourSixPacked0703
import HodgeLean.Foundations.Program.G32PropFourSixPacked0698
import HodgeLean.Foundations.Program.G32PropFourSixPacked0699
import HodgeLean.Foundations.Program.G32PropFourSixPacked0697
import HodgeLean.Foundations.Program.G32PropFourSixPacked0694
import HodgeLean.Foundations.Program.G32PropFourSixPacked0695
import HodgeLean.Foundations.Program.G32PropFourSixPacked0696
import HodgeLean.Foundations.Program.G32PropFourSixPacked0700
import HodgeLean.Foundations.Program.G32PropFourSixSupplierRow18
import HodgeLean.Foundations.Program.G32PropFourSixArchiveReverse

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row18_cosetWordsPart0017 : Fin 4320 → List (Fin 4) :=
  fun i => (if i.val < 2240 then
(if i.val < 2208 then
(if i.val < 2192 then
(if i.val < 2184 then
(if i.val < 2180 then
(if i.val < 2178 then
(if i.val < 2177 then
[0, 1, 2, 3, 2, 2, 1, 1]
else
[0, 1, 2, 3, 2, 2, 1, 3])
else
(if i.val < 2179 then
[0, 1, 2, 3, 2, 2, 3, 0]
else
[0, 1, 2, 3, 3, 0, 0, 2]))
else
(if i.val < 2182 then
(if i.val < 2181 then
[0, 1, 2, 3, 3, 0, 1, 2]
else
[0, 1, 2, 3, 3, 0, 2, 2])
else
(if i.val < 2183 then
[0, 1, 2, 3, 3, 0, 2, 3]
else
[0, 1, 2, 3, 3, 2, 1, 1])))
else
(if i.val < 2188 then
(if i.val < 2186 then
(if i.val < 2185 then
[0, 1, 2, 3, 3, 2, 2, 1]
else
[0, 1, 3, 0, 0, 1, 1, 2])
else
(if i.val < 2187 then
[0, 1, 3, 0, 0, 1, 2, 1]
else
[0, 1, 3, 0, 0, 1, 2, 2]))
else
(if i.val < 2190 then
(if i.val < 2189 then
[0, 1, 3, 0, 0, 1, 2, 3]
else
[0, 1, 3, 0, 0, 1, 3, 2])
else
(if i.val < 2191 then
[0, 1, 3, 0, 0, 2, 3, 2]
else
[0, 1, 3, 0, 0, 3, 2, 1]))))
else
(if i.val < 2200 then
(if i.val < 2196 then
(if i.val < 2194 then
(if i.val < 2193 then
[0, 1, 3, 0, 0, 3, 2, 2]
else
[0, 1, 3, 0, 1, 1, 2, 2])
else
(if i.val < 2195 then
[0, 1, 3, 0, 2, 2, 1, 1]
else
[0, 1, 3, 0, 2, 2, 1, 3]))
else
(if i.val < 2198 then
(if i.val < 2197 then
[0, 1, 3, 2, 1, 0, 3, 2]
else
[0, 1, 3, 2, 1, 1, 2, 3])
else
(if i.val < 2199 then
[0, 1, 3, 2, 2, 1, 1, 3]
else
[0, 1, 3, 2, 2, 3, 0, 0])))
else
(if i.val < 2204 then
(if i.val < 2202 then
(if i.val < 2201 then
[0, 1, 3, 2, 2, 3, 0, 1]
else
[0, 1, 3, 3, 0, 0, 2, 1])
else
(if i.val < 2203 then
[0, 1, 3, 3, 0, 0, 2, 3]
else
[0, 1, 3, 3, 0, 1, 2, 1]))
else
(if i.val < 2206 then
(if i.val < 2205 then
[0, 1, 3, 3, 0, 1, 2, 3]
else
[0, 1, 3, 3, 0, 2, 1, 1])
else
(if i.val < 2207 then
[0, 1, 3, 3, 2, 1, 0, 3]
else
[0, 1, 3, 3, 2, 1, 1, 0])))))
else
(if i.val < 2224 then
(if i.val < 2216 then
(if i.val < 2212 then
(if i.val < 2210 then
(if i.val < 2209 then
[0, 1, 3, 3, 2, 1, 1, 2]
else
[0, 1, 3, 3, 2, 2, 1, 1])
else
(if i.val < 2211 then
[0, 2, 1, 0, 0, 1, 2, 2]
else
[0, 2, 1, 0, 0, 1, 2, 3]))
else
(if i.val < 2214 then
(if i.val < 2213 then
[0, 2, 1, 0, 0, 1, 3, 2]
else
[0, 2, 1, 0, 0, 3, 2, 1])
else
(if i.val < 2215 then
[0, 2, 1, 0, 0, 3, 2, 2]
else
[0, 2, 1, 0, 0, 3, 3, 2])))
else
(if i.val < 2220 then
(if i.val < 2218 then
(if i.val < 2217 then
[0, 2, 1, 0, 3, 2, 1, 0]
else
[0, 2, 1, 0, 3, 2, 1, 1])
else
(if i.val < 2219 then
[0, 2, 1, 0, 3, 2, 2, 3]
else
[0, 2, 1, 0, 3, 3, 0, 1]))
else
(if i.val < 2222 then
(if i.val < 2221 then
[0, 2, 1, 0, 3, 3, 2, 1]
else
[0, 2, 1, 1, 0, 0, 2, 1])
else
(if i.val < 2223 then
[0, 2, 1, 1, 0, 0, 2, 3]
else
[0, 2, 1, 1, 0, 2, 1, 1]))))
else
(if i.val < 2232 then
(if i.val < 2228 then
(if i.val < 2226 then
(if i.val < 2225 then
[0, 2, 1, 1, 0, 2, 1, 3]
else
[0, 2, 1, 1, 0, 2, 3, 0])
else
(if i.val < 2227 then
[0, 2, 1, 1, 0, 2, 3, 2]
else
[0, 2, 1, 1, 0, 2, 3, 3]))
else
(if i.val < 2230 then
(if i.val < 2229 then
[0, 2, 1, 1, 0, 3, 2, 1]
else
[0, 2, 1, 1, 0, 3, 3, 2])
else
(if i.val < 2231 then
[0, 2, 1, 1, 2, 3, 0, 0]
else
[0, 2, 1, 1, 2, 3, 0, 1])))
else
(if i.val < 2236 then
(if i.val < 2234 then
(if i.val < 2233 then
[0, 2, 1, 1, 2, 3, 0, 2]
else
[0, 2, 1, 1, 2, 3, 3, 0])
else
(if i.val < 2235 then
[0, 2, 1, 1, 3, 0, 2, 2]
else
[0, 2, 1, 1, 3, 0, 2, 3]))
else
(if i.val < 2238 then
(if i.val < 2237 then
[0, 2, 1, 1, 3, 2, 2, 1]
else
[0, 2, 1, 1, 3, 2, 2, 3])
else
(if i.val < 2239 then
[0, 2, 1, 1, 3, 3, 0, 2]
else
[0, 2, 1, 3, 0, 0, 1, 2]))))))
else
(if i.val < 2272 then
(if i.val < 2256 then
(if i.val < 2248 then
(if i.val < 2244 then
(if i.val < 2242 then
(if i.val < 2241 then
[0, 2, 1, 3, 0, 0, 3, 2]
else
[0, 2, 1, 3, 3, 0, 1, 2])
else
(if i.val < 2243 then
[0, 2, 1, 3, 3, 0, 2, 2]
else
[0, 2, 1, 3, 3, 0, 2, 3]))
else
(if i.val < 2246 then
(if i.val < 2245 then
[0, 2, 1, 3, 3, 2, 1, 0]
else
[0, 2, 1, 3, 3, 2, 2, 1])
else
(if i.val < 2247 then
[0, 2, 2, 1, 0, 3, 2, 2]
else
[0, 2, 2, 1, 0, 3, 3, 2])))
else
(if i.val < 2252 then
(if i.val < 2250 then
(if i.val < 2249 then
[0, 2, 2, 1, 1, 3, 0, 2]
else
[0, 2, 2, 1, 1, 3, 2, 2])
else
(if i.val < 2251 then
[0, 2, 2, 1, 3, 0, 1, 1]
else
[0, 2, 2, 1, 3, 2, 2, 1]))
else
(if i.val < 2254 then
(if i.val < 2253 then
[0, 2, 2, 1, 3, 2, 2, 3]
else
[0, 2, 2, 1, 3, 3, 0, 2])
else
(if i.val < 2255 then
[0, 2, 2, 1, 3, 3, 2, 1]
else
[0, 2, 2, 1, 3, 3, 2, 2]))))
else
(if i.val < 2264 then
(if i.val < 2260 then
(if i.val < 2258 then
(if i.val < 2257 then
[0, 2, 2, 3, 0, 0, 2, 2]
else
[0, 2, 2, 3, 0, 0, 3, 2])
else
(if i.val < 2259 then
[0, 2, 2, 3, 0, 1, 2, 1]
else
[0, 2, 2, 3, 0, 1, 2, 3]))
else
(if i.val < 2262 then
(if i.val < 2261 then
[0, 2, 2, 3, 0, 2, 1, 0]
else
[0, 2, 2, 3, 0, 2, 1, 1])
else
(if i.val < 2263 then
[0, 2, 2, 3, 0, 2, 2, 1]
else
[0, 2, 2, 3, 0, 2, 3, 3])))
else
(if i.val < 2268 then
(if i.val < 2266 then
(if i.val < 2265 then
[0, 2, 2, 3, 2, 1, 0, 0]
else
[0, 2, 2, 3, 2, 1, 0, 3])
else
(if i.val < 2267 then
[0, 2, 2, 3, 2, 2, 1, 0]
else
[0, 2, 2, 3, 2, 2, 1, 3]))
else
(if i.val < 2270 then
(if i.val < 2269 then
[0, 2, 2, 3, 2, 2, 3, 0]
else
[0, 2, 2, 3, 3, 0, 0, 2])
else
(if i.val < 2271 then
[0, 2, 2, 3, 3, 2, 1, 0]
else
[0, 2, 3, 0, 0, 1, 1, 2])))))
else
(if i.val < 2288 then
(if i.val < 2280 then
(if i.val < 2276 then
(if i.val < 2274 then
(if i.val < 2273 then
[0, 2, 3, 0, 0, 2, 1, 0]
else
[0, 2, 3, 0, 0, 2, 1, 1])
else
(if i.val < 2275 then
[0, 2, 3, 0, 1, 1, 0, 2]
else
[0, 2, 3, 0, 1, 1, 2, 1]))
else
(if i.val < 2278 then
(if i.val < 2277 then
[0, 2, 3, 0, 1, 1, 2, 3]
else
[0, 2, 3, 0, 1, 2, 1, 3])
else
(if i.val < 2279 then
[0, 2, 3, 0, 1, 2, 2, 3]
else
[0, 2, 3, 0, 1, 2, 3, 0])))
else
(if i.val < 2284 then
(if i.val < 2282 then
(if i.val < 2281 then
[0, 2, 3, 0, 1, 2, 3, 3]
else
[0, 2, 3, 0, 2, 1, 0, 3])
else
(if i.val < 2283 then
[0, 2, 3, 0, 2, 1, 1, 2]
else
[0, 2, 3, 0, 2, 1, 3, 3]))
else
(if i.val < 2286 then
(if i.val < 2285 then
[0, 2, 3, 0, 2, 2, 1, 3]
else
[0, 2, 3, 0, 2, 2, 3, 3])
else
(if i.val < 2287 then
[0, 2, 3, 0, 2, 3, 3, 0]
else
[0, 2, 3, 0, 2, 3, 3, 2]))))
else
(if i.val < 2296 then
(if i.val < 2292 then
(if i.val < 2290 then
(if i.val < 2289 then
[0, 2, 3, 2, 1, 0, 3, 2]
else
[0, 2, 3, 2, 1, 0, 3, 3])
else
(if i.val < 2291 then
[0, 2, 3, 2, 1, 1, 0, 0]
else
[0, 2, 3, 2, 2, 1, 0, 0]))
else
(if i.val < 2294 then
(if i.val < 2293 then
[0, 2, 3, 2, 2, 1, 1, 0]
else
[0, 2, 3, 2, 2, 1, 1, 3])
else
(if i.val < 2295 then
[0, 2, 3, 2, 2, 3, 0, 0]
else
[0, 2, 3, 2, 2, 3, 0, 1])))
else
(if i.val < 2300 then
(if i.val < 2298 then
(if i.val < 2297 then
[0, 2, 3, 3, 0, 0, 2, 1]
else
[0, 2, 3, 3, 0, 0, 2, 3])
else
(if i.val < 2299 then
[0, 2, 3, 3, 0, 1, 1, 2]
else
[0, 2, 3, 3, 0, 1, 2, 1]))
else
(if i.val < 2302 then
(if i.val < 2301 then
[0, 2, 3, 3, 0, 2, 1, 1]
else
[0, 2, 3, 3, 0, 2, 1, 3])
else
(if i.val < 2303 then
[0, 2, 3, 3, 0, 2, 3, 3]
else
[0, 2, 3, 3, 2, 1, 0, 0])))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row18_cosetWordsPart0018 : Fin 4320 → List (Fin 4) :=
  fun i => (if i.val < 2368 then
(if i.val < 2336 then
(if i.val < 2320 then
(if i.val < 2312 then
(if i.val < 2308 then
(if i.val < 2306 then
(if i.val < 2305 then
[0, 2, 3, 3, 2, 1, 0, 3]
else
[0, 3, 0, 0, 1, 1, 2, 1])
else
(if i.val < 2307 then
[0, 3, 0, 0, 1, 1, 2, 2]
else
[0, 3, 0, 0, 1, 1, 2, 3]))
else
(if i.val < 2310 then
(if i.val < 2309 then
[0, 3, 0, 0, 1, 2, 1, 1]
else
[0, 3, 0, 0, 1, 2, 3, 3])
else
(if i.val < 2311 then
[0, 3, 0, 0, 1, 3, 2, 1]
else
[0, 3, 0, 0, 1, 3, 2, 2])))
else
(if i.val < 2316 then
(if i.val < 2314 then
(if i.val < 2313 then
[0, 3, 0, 0, 2, 1, 0, 0]
else
[0, 3, 0, 0, 2, 2, 1, 0])
else
(if i.val < 2315 then
[0, 3, 0, 0, 2, 2, 1, 3]
else
[0, 3, 0, 0, 2, 2, 3, 2]))
else
(if i.val < 2318 then
(if i.val < 2317 then
[0, 3, 0, 0, 2, 3, 2, 1]
else
[0, 3, 0, 0, 2, 3, 3, 2])
else
(if i.val < 2319 then
[0, 3, 0, 0, 3, 2, 1, 0]
else
[0, 3, 0, 0, 3, 2, 1, 1]))))
else
(if i.val < 2328 then
(if i.val < 2324 then
(if i.val < 2322 then
(if i.val < 2321 then
[0, 3, 0, 0, 3, 2, 2, 1]
else
[0, 3, 0, 1, 1, 0, 2, 1])
else
(if i.val < 2323 then
[0, 3, 0, 1, 1, 0, 2, 2]
else
[0, 3, 0, 1, 1, 0, 2, 3]))
else
(if i.val < 2326 then
(if i.val < 2325 then
[0, 3, 0, 1, 1, 0, 3, 2]
else
[0, 3, 0, 1, 1, 2, 1, 0])
else
(if i.val < 2327 then
[0, 3, 0, 1, 1, 2, 1, 1]
else
[0, 3, 0, 1, 1, 2, 2, 1])))
else
(if i.val < 2332 then
(if i.val < 2330 then
(if i.val < 2329 then
[0, 3, 0, 1, 1, 2, 2, 3]
else
[0, 3, 0, 1, 1, 2, 3, 0])
else
(if i.val < 2331 then
[0, 3, 0, 1, 2, 1, 1, 0]
else
[0, 3, 0, 1, 2, 1, 1, 2]))
else
(if i.val < 2334 then
(if i.val < 2333 then
[0, 3, 0, 1, 2, 1, 1, 3]
else
[0, 3, 0, 1, 2, 1, 3, 3])
else
(if i.val < 2335 then
[0, 3, 0, 1, 2, 2, 3, 0]
else
[0, 3, 0, 1, 2, 2, 3, 3])))))
else
(if i.val < 2352 then
(if i.val < 2344 then
(if i.val < 2340 then
(if i.val < 2338 then
(if i.val < 2337 then
[0, 3, 0, 1, 2, 3, 0, 1]
else
[0, 3, 0, 1, 2, 3, 3, 0])
else
(if i.val < 2339 then
[0, 3, 0, 1, 2, 3, 3, 2]
else
[0, 3, 0, 2, 1, 0, 3, 3]))
else
(if i.val < 2342 then
(if i.val < 2341 then
[0, 3, 0, 2, 1, 1, 0, 2]
else
[0, 3, 0, 2, 1, 1, 0, 3])
else
(if i.val < 2343 then
[0, 3, 0, 2, 1, 1, 2, 3]
else
[0, 3, 0, 2, 1, 3, 3, 0])))
else
(if i.val < 2348 then
(if i.val < 2346 then
(if i.val < 2345 then
[0, 3, 0, 2, 2, 1, 0, 0]
else
[0, 3, 0, 2, 2, 1, 1, 0])
else
(if i.val < 2347 then
[0, 3, 0, 2, 2, 1, 3, 3]
else
[0, 3, 0, 2, 2, 3, 3, 0]))
else
(if i.val < 2350 then
(if i.val < 2349 then
[0, 3, 0, 2, 3, 3, 0, 1]
else
[0, 3, 0, 2, 3, 3, 0, 2])
else
(if i.val < 2351 then
[0, 3, 0, 2, 3, 3, 2, 1]
else
[0, 3, 2, 1, 0, 0, 1, 3]))))
else
(if i.val < 2360 then
(if i.val < 2356 then
(if i.val < 2354 then
(if i.val < 2353 then
[0, 3, 2, 1, 0, 0, 3, 2]
else
[0, 3, 2, 1, 0, 3, 2, 1])
else
(if i.val < 2355 then
[0, 3, 2, 1, 0, 3, 2, 2]
else
[0, 3, 2, 1, 1, 0, 0, 2]))
else
(if i.val < 2358 then
(if i.val < 2357 then
[0, 3, 2, 1, 1, 0, 2, 1]
else
[0, 3, 2, 1, 1, 0, 2, 3])
else
(if i.val < 2359 then
[0, 3, 2, 1, 1, 0, 3, 2]
else
[0, 3, 2, 1, 1, 0, 3, 3])))
else
(if i.val < 2364 then
(if i.val < 2362 then
(if i.val < 2361 then
[0, 3, 2, 1, 1, 2, 3, 0]
else
[0, 3, 2, 2, 1, 0, 0, 3])
else
(if i.val < 2363 then
[0, 3, 2, 2, 1, 0, 3, 2]
else
[0, 3, 2, 2, 1, 0, 3, 3]))
else
(if i.val < 2366 then
(if i.val < 2365 then
[0, 3, 2, 2, 1, 1, 0, 0]
else
[0, 3, 2, 2, 1, 1, 3, 0])
else
(if i.val < 2367 then
[0, 3, 2, 2, 1, 3, 0, 0]
else
[0, 3, 2, 2, 1, 3, 0, 1]))))))
else
(if i.val < 2400 then
(if i.val < 2384 then
(if i.val < 2376 then
(if i.val < 2372 then
(if i.val < 2370 then
(if i.val < 2369 then
[0, 3, 2, 2, 1, 3, 0, 2]
else
[0, 3, 2, 2, 3, 0, 0, 3])
else
(if i.val < 2371 then
[0, 3, 2, 2, 3, 0, 1, 1]
else
[0, 3, 2, 2, 3, 0, 1, 2]))
else
(if i.val < 2374 then
(if i.val < 2373 then
[0, 3, 3, 0, 0, 2, 1, 3]
else
[0, 3, 3, 0, 1, 1, 0, 2])
else
(if i.val < 2375 then
[0, 3, 3, 0, 1, 1, 2, 3]
else
[0, 3, 3, 0, 1, 2, 1, 0])))
else
(if i.val < 2380 then
(if i.val < 2378 then
(if i.val < 2377 then
[0, 3, 3, 0, 1, 2, 1, 1]
else
[0, 3, 3, 0, 1, 2, 1, 3])
else
(if i.val < 2379 then
[0, 3, 3, 0, 1, 2, 2, 1]
else
[0, 3, 3, 0, 1, 2, 2, 3]))
else
(if i.val < 2382 then
(if i.val < 2381 then
[0, 3, 3, 0, 1, 2, 3, 0]
else
[0, 3, 3, 0, 2, 1, 0, 0])
else
(if i.val < 2383 then
[0, 3, 3, 0, 2, 1, 1, 2]
else
[0, 3, 3, 0, 2, 3, 3, 2]))))
else
(if i.val < 2392 then
(if i.val < 2388 then
(if i.val < 2386 then
(if i.val < 2385 then
[0, 3, 3, 2, 1, 0, 0, 3]
else
[0, 3, 3, 2, 1, 0, 3, 3])
else
(if i.val < 2387 then
[1, 0, 0, 1, 2, 1, 0, 0]
else
[1, 0, 0, 1, 2, 1, 0, 3]))
else
(if i.val < 2390 then
(if i.val < 2389 then
[1, 0, 0, 1, 2, 1, 1, 0]
else
[1, 0, 0, 1, 2, 1, 1, 2])
else
(if i.val < 2391 then
[1, 0, 0, 1, 2, 1, 1, 3]
else
[1, 0, 0, 1, 2, 1, 3, 0])))
else
(if i.val < 2396 then
(if i.val < 2394 then
(if i.val < 2393 then
[1, 0, 0, 1, 2, 1, 3, 3]
else
[1, 0, 0, 1, 2, 2, 1, 0])
else
(if i.val < 2395 then
[1, 0, 0, 1, 2, 2, 1, 3]
else
[1, 0, 0, 1, 2, 3, 0, 0]))
else
(if i.val < 2398 then
(if i.val < 2397 then
[1, 0, 0, 1, 2, 3, 0, 1]
else
[1, 0, 0, 1, 2, 3, 0, 2])
else
(if i.val < 2399 then
[1, 0, 0, 1, 2, 3, 2, 2]
else
[1, 0, 0, 1, 2, 3, 3, 2])))))
else
(if i.val < 2416 then
(if i.val < 2408 then
(if i.val < 2404 then
(if i.val < 2402 then
(if i.val < 2401 then
[1, 0, 0, 1, 3, 2, 2, 1]
else
[1, 0, 0, 1, 3, 2, 2, 3])
else
(if i.val < 2403 then
[1, 0, 0, 1, 3, 3, 0, 2]
else
[1, 0, 0, 2, 1, 0, 3, 0]))
else
(if i.val < 2406 then
(if i.val < 2405 then
[1, 0, 0, 2, 1, 0, 3, 3]
else
[1, 0, 0, 2, 1, 1, 0, 2])
else
(if i.val < 2407 then
[1, 0, 0, 2, 1, 1, 0, 3]
else
[1, 0, 0, 2, 1, 1, 2, 3])))
else
(if i.val < 2412 then
(if i.val < 2410 then
(if i.val < 2409 then
[1, 0, 0, 2, 1, 3, 0, 1]
else
[1, 0, 0, 2, 1, 3, 3, 2])
else
(if i.val < 2411 then
[1, 0, 0, 2, 2, 1, 0, 0]
else
[1, 0, 0, 2, 2, 3, 2, 1]))
else
(if i.val < 2414 then
(if i.val < 2413 then
[1, 0, 0, 2, 3, 0, 0, 2]
else
[1, 0, 0, 2, 3, 0, 0, 3])
else
(if i.val < 2415 then
[1, 0, 0, 2, 3, 0, 1, 1]
else
[1, 0, 0, 2, 3, 0, 2, 1]))))
else
(if i.val < 2424 then
(if i.val < 2420 then
(if i.val < 2418 then
(if i.val < 2417 then
[1, 0, 0, 2, 3, 0, 2, 2]
else
[1, 0, 0, 2, 3, 0, 2, 3])
else
(if i.val < 2419 then
[1, 0, 0, 2, 3, 2, 1, 1]
else
[1, 0, 0, 2, 3, 2, 2, 1]))
else
(if i.val < 2422 then
(if i.val < 2421 then
[1, 0, 0, 2, 3, 3, 2, 2]
else
[1, 0, 0, 3, 0, 0, 2, 1])
else
(if i.val < 2423 then
[1, 0, 0, 3, 0, 0, 3, 2]
else
[1, 0, 0, 3, 0, 1, 2, 1])))
else
(if i.val < 2428 then
(if i.val < 2426 then
(if i.val < 2425 then
[1, 0, 0, 3, 0, 1, 2, 3]
else
[1, 0, 0, 3, 0, 2, 1, 0])
else
(if i.val < 2427 then
[1, 0, 0, 3, 0, 2, 1, 1]
else
[1, 0, 0, 3, 0, 2, 2, 1]))
else
(if i.val < 2430 then
(if i.val < 2429 then
[1, 0, 0, 3, 2, 1, 1, 2]
else
[1, 0, 0, 3, 2, 2, 1, 3])
else
(if i.val < 2431 then
[1, 0, 0, 3, 3, 0, 0, 2]
else
[1, 0, 0, 3, 3, 0, 2, 1])))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row18_cosetWordsPart0019 : Fin 4320 → List (Fin 4) :=
  fun i => (if i.val < 2496 then
(if i.val < 2464 then
(if i.val < 2448 then
(if i.val < 2440 then
(if i.val < 2436 then
(if i.val < 2434 then
(if i.val < 2433 then
[1, 0, 0, 3, 3, 0, 2, 2]
else
[1, 0, 0, 3, 3, 0, 2, 3])
else
(if i.val < 2435 then
[1, 0, 0, 3, 3, 2, 1, 0]
else
[1, 0, 0, 3, 3, 2, 2, 1]))
else
(if i.val < 2438 then
(if i.val < 2437 then
[1, 0, 2, 1, 0, 0, 1, 2]
else
[1, 0, 2, 1, 0, 0, 1, 3])
else
(if i.val < 2439 then
[1, 0, 2, 1, 0, 3, 3, 2]
else
[1, 0, 2, 1, 1, 0, 0, 2])))
else
(if i.val < 2444 then
(if i.val < 2442 then
(if i.val < 2441 then
[1, 0, 2, 1, 1, 0, 2, 1]
else
[1, 0, 2, 1, 1, 0, 2, 3])
else
(if i.val < 2443 then
[1, 0, 2, 1, 1, 0, 3, 2]
else
[1, 0, 2, 1, 1, 2, 3, 0]))
else
(if i.val < 2446 then
(if i.val < 2445 then
[1, 0, 2, 1, 1, 2, 3, 3]
else
[1, 0, 2, 1, 1, 3, 0, 2])
else
(if i.val < 2447 then
[1, 0, 2, 1, 1, 3, 2, 2]
else
[1, 0, 2, 1, 1, 3, 3, 2]))))
else
(if i.val < 2456 then
(if i.val < 2452 then
(if i.val < 2450 then
(if i.val < 2449 then
[1, 0, 2, 1, 3, 3, 0, 1]
else
[1, 0, 2, 1, 3, 3, 2, 1])
else
(if i.val < 2451 then
[1, 0, 2, 1, 3, 3, 2, 2]
else
[1, 0, 2, 2, 1, 0, 0, 3]))
else
(if i.val < 2454 then
(if i.val < 2453 then
[1, 0, 2, 2, 1, 0, 3, 2]
else
[1, 0, 2, 2, 1, 0, 3, 3])
else
(if i.val < 2455 then
[1, 0, 2, 2, 1, 1, 3, 0]
else
[1, 0, 2, 2, 1, 3, 0, 0])))
else
(if i.val < 2460 then
(if i.val < 2458 then
(if i.val < 2457 then
[1, 0, 2, 2, 1, 3, 0, 1]
else
[1, 0, 2, 2, 1, 3, 3, 0])
else
(if i.val < 2459 then
[1, 0, 2, 2, 1, 3, 3, 2]
else
[1, 0, 2, 2, 3, 0, 0, 2]))
else
(if i.val < 2462 then
(if i.val < 2461 then
[1, 0, 2, 2, 3, 0, 0, 3]
else
[1, 0, 2, 2, 3, 0, 1, 2])
else
(if i.val < 2463 then
[1, 0, 2, 2, 3, 0, 2, 1]
else
[1, 0, 2, 2, 3, 0, 2, 2])))))
else
(if i.val < 2480 then
(if i.val < 2472 then
(if i.val < 2468 then
(if i.val < 2466 then
(if i.val < 2465 then
[1, 0, 2, 2, 3, 0, 2, 3]
else
[1, 0, 2, 2, 3, 2, 1, 0])
else
(if i.val < 2467 then
[1, 0, 2, 2, 3, 2, 1, 1]
else
[1, 0, 2, 2, 3, 2, 2, 1]))
else
(if i.val < 2470 then
(if i.val < 2469 then
[1, 0, 2, 2, 3, 2, 2, 3]
else
[1, 0, 2, 2, 3, 3, 0, 1])
else
(if i.val < 2471 then
[1, 0, 2, 3, 0, 0, 2, 3]
else
[1, 0, 2, 3, 0, 1, 1, 2])))
else
(if i.val < 2476 then
(if i.val < 2474 then
(if i.val < 2473 then
[1, 0, 2, 3, 0, 1, 2, 1]
else
[1, 0, 2, 3, 0, 1, 2, 2])
else
(if i.val < 2475 then
[1, 0, 2, 3, 0, 1, 2, 3]
else
[1, 0, 2, 3, 0, 2, 1, 0]))
else
(if i.val < 2478 then
(if i.val < 2477 then
[1, 0, 2, 3, 0, 2, 1, 1]
else
[1, 0, 2, 3, 0, 2, 1, 3])
else
(if i.val < 2479 then
[1, 0, 2, 3, 0, 2, 2, 1]
else
[1, 0, 2, 3, 2, 1, 0, 0]))))
else
(if i.val < 2488 then
(if i.val < 2484 then
(if i.val < 2482 then
(if i.val < 2481 then
[1, 0, 2, 3, 2, 1, 0, 3]
else
[1, 0, 2, 3, 2, 1, 1, 0])
else
(if i.val < 2483 then
[1, 0, 2, 3, 2, 2, 3, 0]
else
[1, 0, 2, 3, 3, 0, 0, 2]))
else
(if i.val < 2486 then
(if i.val < 2485 then
[1, 0, 2, 3, 3, 0, 1, 2]
else
[1, 0, 2, 3, 3, 0, 2, 1])
else
(if i.val < 2487 then
[1, 0, 2, 3, 3, 0, 2, 2]
else
[1, 0, 2, 3, 3, 0, 2, 3])))
else
(if i.val < 2492 then
(if i.val < 2490 then
(if i.val < 2489 then
[1, 0, 2, 3, 3, 2, 1, 0]
else
[1, 0, 2, 3, 3, 2, 1, 1])
else
(if i.val < 2491 then
[1, 0, 3, 0, 0, 1, 1, 2]
else
[1, 0, 3, 0, 0, 1, 3, 2]))
else
(if i.val < 2494 then
(if i.val < 2493 then
[1, 0, 3, 0, 0, 2, 1, 0]
else
[1, 0, 3, 0, 0, 2, 1, 1])
else
(if i.val < 2495 then
[1, 0, 3, 0, 0, 2, 2, 1]
else
[1, 0, 3, 0, 0, 2, 3, 2]))))))
else
(if i.val < 2528 then
(if i.val < 2512 then
(if i.val < 2504 then
(if i.val < 2500 then
(if i.val < 2498 then
(if i.val < 2497 then
[1, 0, 3, 0, 0, 2, 3, 3]
else
[1, 0, 3, 0, 0, 3, 2, 1])
else
(if i.val < 2499 then
[1, 0, 3, 0, 0, 3, 2, 2]
else
[1, 0, 3, 0, 1, 1, 0, 2]))
else
(if i.val < 2502 then
(if i.val < 2501 then
[1, 0, 3, 0, 1, 1, 2, 1]
else
[1, 0, 3, 0, 1, 1, 2, 3])
else
(if i.val < 2503 then
[1, 0, 3, 0, 1, 2, 1, 0]
else
[1, 0, 3, 0, 1, 2, 1, 1])))
else
(if i.val < 2508 then
(if i.val < 2506 then
(if i.val < 2505 then
[1, 0, 3, 0, 1, 2, 3, 3]
else
[1, 0, 3, 0, 2, 1, 0, 0])
else
(if i.val < 2507 then
[1, 0, 3, 0, 2, 1, 0, 3]
else
[1, 0, 3, 0, 2, 1, 1, 0]))
else
(if i.val < 2510 then
(if i.val < 2509 then
[1, 0, 3, 0, 2, 1, 1, 2]
else
[1, 0, 3, 0, 2, 2, 1, 3])
else
(if i.val < 2511 then
[1, 0, 3, 0, 2, 2, 3, 3]
else
[1, 0, 3, 0, 2, 3, 3, 0]))))
else
(if i.val < 2520 then
(if i.val < 2516 then
(if i.val < 2514 then
(if i.val < 2513 then
[1, 0, 3, 0, 2, 3, 3, 2]
else
[1, 0, 3, 2, 1, 0, 0, 3])
else
(if i.val < 2515 then
[1, 0, 3, 2, 1, 0, 3, 2]
else
[1, 0, 3, 2, 1, 1, 0, 0]))
else
(if i.val < 2518 then
(if i.val < 2517 then
[1, 0, 3, 2, 1, 1, 0, 2]
else
[1, 0, 3, 2, 1, 1, 0, 3])
else
(if i.val < 2519 then
[1, 0, 3, 2, 1, 1, 2, 3]
else
[1, 0, 3, 2, 2, 1, 1, 3])))
else
(if i.val < 2524 then
(if i.val < 2522 then
(if i.val < 2521 then
[1, 0, 3, 2, 2, 3, 0, 0]
else
[1, 0, 3, 2, 2, 3, 0, 1])
else
(if i.val < 2523 then
[1, 0, 3, 3, 0, 1, 2, 1]
else
[1, 0, 3, 3, 0, 1, 2, 2]))
else
(if i.val < 2526 then
(if i.val < 2525 then
[1, 0, 3, 3, 2, 1, 0, 3]
else
[1, 0, 3, 3, 2, 1, 1, 2])
else
(if i.val < 2527 then
[1, 0, 3, 3, 2, 2, 1, 1]
else
[1, 1, 0, 0, 2, 1, 0, 0])))))
else
(if i.val < 2544 then
(if i.val < 2536 then
(if i.val < 2532 then
(if i.val < 2530 then
(if i.val < 2529 then
[1, 1, 0, 0, 2, 1, 1, 2]
else
[1, 1, 0, 0, 2, 1, 1, 3])
else
(if i.val < 2531 then
[1, 1, 0, 0, 2, 1, 3, 3]
else
[1, 1, 0, 0, 2, 3, 0, 0]))
else
(if i.val < 2534 then
(if i.val < 2533 then
[1, 1, 0, 0, 2, 3, 0, 1]
else
[1, 1, 0, 0, 2, 3, 0, 2])
else
(if i.val < 2535 then
[1, 1, 0, 0, 2, 3, 3, 2]
else
[1, 1, 0, 0, 3, 0, 1, 2])))
else
(if i.val < 2540 then
(if i.val < 2538 then
(if i.val < 2537 then
[1, 1, 0, 0, 3, 0, 2, 1]
else
[1, 1, 0, 2, 1, 0, 3, 3])
else
(if i.val < 2539 then
[1, 1, 0, 2, 1, 1, 2, 3]
else
[1, 1, 0, 2, 1, 1, 3, 3]))
else
(if i.val < 2542 then
(if i.val < 2541 then
[1, 1, 0, 2, 2, 1, 3, 3]
else
[1, 1, 0, 2, 2, 3, 2, 1])
else
(if i.val < 2543 then
[1, 1, 0, 2, 2, 3, 3, 2]
else
[1, 1, 0, 2, 3, 0, 0, 2]))))
else
(if i.val < 2552 then
(if i.val < 2548 then
(if i.val < 2546 then
(if i.val < 2545 then
[1, 1, 0, 2, 3, 0, 0, 3]
else
[1, 1, 0, 2, 3, 0, 1, 1])
else
(if i.val < 2547 then
[1, 1, 0, 2, 3, 0, 2, 1]
else
[1, 1, 0, 2, 3, 0, 2, 2]))
else
(if i.val < 2550 then
(if i.val < 2549 then
[1, 1, 0, 2, 3, 0, 2, 3]
else
[1, 1, 0, 2, 3, 2, 1, 1])
else
(if i.val < 2551 then
[1, 1, 0, 2, 3, 3, 2, 1]
else
[1, 1, 0, 3, 0, 0, 2, 1])))
else
(if i.val < 2556 then
(if i.val < 2554 then
(if i.val < 2553 then
[1, 1, 0, 3, 0, 0, 2, 3]
else
[1, 1, 0, 3, 0, 0, 3, 2])
else
(if i.val < 2555 then
[1, 1, 0, 3, 0, 1, 1, 2]
else
[1, 1, 0, 3, 0, 1, 2, 1]))
else
(if i.val < 2558 then
(if i.val < 2557 then
[1, 1, 0, 3, 0, 2, 1, 1]
else
[1, 1, 0, 3, 0, 2, 2, 1])
else
(if i.val < 2559 then
[1, 1, 0, 3, 2, 1, 0, 0]
else
[1, 1, 0, 3, 2, 1, 1, 0])))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row18_cosetWordsPart0020 : Fin 4320 → List (Fin 4) :=
  fun i => (if i.val < 2624 then
(if i.val < 2592 then
(if i.val < 2576 then
(if i.val < 2568 then
(if i.val < 2564 then
(if i.val < 2562 then
(if i.val < 2561 then
[1, 1, 0, 3, 2, 1, 1, 2]
else
[1, 1, 0, 3, 2, 2, 1, 0])
else
(if i.val < 2563 then
[1, 1, 0, 3, 2, 2, 1, 3]
else
[1, 1, 0, 3, 3, 0, 1, 2]))
else
(if i.val < 2566 then
(if i.val < 2565 then
[1, 1, 0, 3, 3, 0, 2, 1]
else
[1, 1, 0, 3, 3, 0, 2, 3])
else
(if i.val < 2567 then
[1, 1, 2, 1, 0, 0, 1, 2]
else
[1, 1, 2, 1, 0, 0, 1, 3])))
else
(if i.val < 2572 then
(if i.val < 2570 then
(if i.val < 2569 then
[1, 1, 2, 1, 0, 3, 0, 0]
else
[1, 1, 2, 1, 0, 3, 0, 1])
else
(if i.val < 2571 then
[1, 1, 2, 1, 0, 3, 0, 2]
else
[1, 1, 2, 1, 0, 3, 2, 2]))
else
(if i.val < 2574 then
(if i.val < 2573 then
[1, 1, 2, 1, 0, 3, 3, 2]
else
[1, 1, 2, 1, 1, 0, 2, 3])
else
(if i.val < 2575 then
[1, 1, 2, 1, 1, 0, 3, 2]
else
[1, 1, 2, 1, 1, 0, 3, 3]))))
else
(if i.val < 2584 then
(if i.val < 2580 then
(if i.val < 2578 then
(if i.val < 2577 then
[1, 1, 2, 1, 1, 2, 3, 3]
else
[1, 1, 2, 1, 1, 3, 0, 0])
else
(if i.val < 2579 then
[1, 1, 2, 1, 1, 3, 0, 1]
else
[1, 1, 2, 1, 1, 3, 2, 2]))
else
(if i.val < 2582 then
(if i.val < 2581 then
[1, 1, 2, 1, 3, 2, 2, 1]
else
[1, 1, 2, 1, 3, 2, 2, 3])
else
(if i.val < 2583 then
[1, 1, 2, 1, 3, 3, 0, 0]
else
[1, 1, 2, 1, 3, 3, 0, 1])))
else
(if i.val < 2588 then
(if i.val < 2586 then
(if i.val < 2585 then
[1, 1, 2, 1, 3, 3, 2, 2]
else
[1, 1, 2, 2, 1, 0, 3, 3])
else
(if i.val < 2587 then
[1, 1, 2, 2, 1, 3, 0, 2]
else
[1, 1, 2, 2, 1, 3, 3, 2]))
else
(if i.val < 2590 then
(if i.val < 2589 then
[1, 1, 2, 2, 3, 0, 1, 2]
else
[1, 1, 2, 2, 3, 2, 1, 0])
else
(if i.val < 2591 then
[1, 1, 2, 2, 3, 2, 1, 1]
else
[1, 1, 2, 2, 3, 2, 2, 1])))))
else
(if i.val < 2608 then
(if i.val < 2600 then
(if i.val < 2596 then
(if i.val < 2594 then
(if i.val < 2593 then
[1, 1, 2, 2, 3, 2, 2, 3]
else
[1, 1, 2, 2, 3, 3, 2, 1])
else
(if i.val < 2595 then
[1, 1, 2, 3, 0, 0, 2, 3]
else
[1, 1, 2, 3, 0, 1, 1, 2]))
else
(if i.val < 2598 then
(if i.val < 2597 then
[1, 1, 2, 3, 0, 2, 2, 1]
else
[1, 1, 2, 3, 2, 1, 0, 3])
else
(if i.val < 2599 then
[1, 1, 2, 3, 3, 0, 1, 2]
else
[1, 1, 2, 3, 3, 0, 2, 3])))
else
(if i.val < 2604 then
(if i.val < 2602 then
(if i.val < 2601 then
[1, 1, 3, 0, 0, 1, 1, 2]
else
[1, 1, 3, 0, 0, 2, 3, 2])
else
(if i.val < 2603 then
[1, 1, 3, 0, 0, 2, 3, 3]
else
[1, 1, 3, 0, 0, 3, 2, 1]))
else
(if i.val < 2606 then
(if i.val < 2605 then
[1, 1, 3, 0, 1, 1, 0, 2]
else
[1, 1, 3, 0, 1, 1, 2, 1])
else
(if i.val < 2607 then
[1, 1, 3, 0, 1, 1, 2, 2]
else
[1, 1, 3, 0, 1, 1, 2, 3]))))
else
(if i.val < 2616 then
(if i.val < 2612 then
(if i.val < 2610 then
(if i.val < 2609 then
[1, 1, 3, 0, 1, 2, 1, 0]
else
[1, 1, 3, 0, 1, 2, 1, 1])
else
(if i.val < 2611 then
[1, 1, 3, 0, 1, 2, 2, 1]
else
[1, 1, 3, 0, 1, 2, 3, 3]))
else
(if i.val < 2614 then
(if i.val < 2613 then
[1, 1, 3, 0, 2, 1, 1, 2]
else
[1, 1, 3, 0, 2, 2, 1, 3])
else
(if i.val < 2615 then
[1, 1, 3, 0, 2, 3, 3, 2]
else
[1, 1, 3, 2, 1, 0, 0, 3])))
else
(if i.val < 2620 then
(if i.val < 2618 then
(if i.val < 2617 then
[1, 1, 3, 2, 1, 0, 3, 2]
else
[1, 1, 3, 2, 1, 1, 2, 3])
else
(if i.val < 2619 then
[1, 1, 3, 2, 2, 1, 1, 3]
else
[1, 1, 3, 3, 0, 1, 2, 1]))
else
(if i.val < 2622 then
(if i.val < 2621 then
[1, 1, 3, 3, 0, 1, 2, 2]
else
[1, 1, 3, 3, 0, 1, 2, 3])
else
(if i.val < 2623 then
[1, 1, 3, 3, 2, 1, 0, 3]
else
[1, 2, 1, 0, 0, 1, 2, 3]))))))
else
(if i.val < 2656 then
(if i.val < 2640 then
(if i.val < 2632 then
(if i.val < 2628 then
(if i.val < 2626 then
(if i.val < 2625 then
[1, 2, 1, 0, 0, 3, 2, 2]
else
[1, 2, 1, 0, 3, 0, 2, 2])
else
(if i.val < 2627 then
[1, 2, 1, 0, 3, 3, 0, 1]
else
[1, 2, 1, 1, 0, 0, 3, 2]))
else
(if i.val < 2630 then
(if i.val < 2629 then
[1, 2, 1, 1, 0, 2, 1, 3]
else
[1, 2, 1, 1, 0, 2, 3, 0])
else
(if i.val < 2631 then
[1, 2, 1, 1, 0, 2, 3, 2]
else
[1, 2, 1, 1, 0, 3, 0, 2])))
else
(if i.val < 2636 then
(if i.val < 2634 then
(if i.val < 2633 then
[1, 2, 1, 1, 0, 3, 3, 2]
else
[1, 2, 1, 1, 2, 3, 0, 0])
else
(if i.val < 2635 then
[1, 2, 1, 1, 2, 3, 0, 1]
else
[1, 2, 1, 1, 2, 3, 2, 2]))
else
(if i.val < 2638 then
(if i.val < 2637 then
[1, 2, 1, 1, 2, 3, 3, 0]
else
[1, 2, 1, 1, 3, 0, 1, 2])
else
(if i.val < 2639 then
[1, 2, 1, 1, 3, 0, 2, 2]
else
[1, 2, 1, 1, 3, 2, 2, 1]))))
else
(if i.val < 2648 then
(if i.val < 2644 then
(if i.val < 2642 then
(if i.val < 2641 then
[1, 2, 1, 1, 3, 2, 2, 3]
else
[1, 2, 1, 3, 0, 0, 1, 2])
else
(if i.val < 2643 then
[1, 2, 1, 3, 0, 1, 2, 2]
else
[1, 2, 1, 3, 2, 2, 1, 3]))
else
(if i.val < 2646 then
(if i.val < 2645 then
[1, 2, 1, 3, 2, 2, 3, 0]
else
[1, 2, 1, 3, 3, 0, 1, 2])
else
(if i.val < 2647 then
[1, 2, 1, 3, 3, 0, 2, 2]
else
[1, 2, 1, 3, 3, 2, 2, 1])))
else
(if i.val < 2652 then
(if i.val < 2650 then
(if i.val < 2649 then
[1, 2, 2, 1, 0, 0, 1, 2]
else
[1, 2, 2, 1, 0, 0, 1, 3])
else
(if i.val < 2651 then
[1, 2, 2, 1, 0, 0, 3, 2]
else
[1, 2, 2, 1, 0, 3, 0, 2]))
else
(if i.val < 2654 then
(if i.val < 2653 then
[1, 2, 2, 1, 0, 3, 2, 1]
else
[1, 2, 2, 1, 1, 3, 0, 0])
else
(if i.val < 2655 then
[1, 2, 2, 1, 1, 3, 0, 2]
else
[1, 2, 2, 1, 3, 0, 1, 1])))))
else
(if i.val < 2672 then
(if i.val < 2664 then
(if i.val < 2660 then
(if i.val < 2658 then
(if i.val < 2657 then
[1, 2, 2, 1, 3, 0, 1, 2]
else
[1, 2, 2, 1, 3, 3, 0, 1])
else
(if i.val < 2659 then
[1, 2, 2, 1, 3, 3, 0, 2]
else
[1, 2, 2, 1, 3, 3, 2, 1]))
else
(if i.val < 2662 then
(if i.val < 2661 then
[1, 2, 2, 3, 0, 0, 1, 2]
else
[1, 2, 2, 3, 0, 0, 3, 2])
else
(if i.val < 2663 then
[1, 2, 2, 3, 0, 2, 2, 1]
else
[1, 2, 2, 3, 2, 2, 1, 1])))
else
(if i.val < 2668 then
(if i.val < 2666 then
(if i.val < 2665 then
[1, 2, 2, 3, 2, 2, 1, 3]
else
[1, 2, 2, 3, 3, 0, 0, 2])
else
(if i.val < 2667 then
[1, 2, 2, 3, 3, 2, 1, 0]
else
[1, 2, 3, 0, 0, 1, 1, 2]))
else
(if i.val < 2670 then
(if i.val < 2669 then
[1, 2, 3, 0, 0, 1, 2, 1]
else
[1, 2, 3, 0, 0, 1, 2, 3])
else
(if i.val < 2671 then
[1, 2, 3, 0, 0, 3, 2, 2]
else
[1, 2, 3, 0, 1, 1, 2, 1]))))
else
(if i.val < 2680 then
(if i.val < 2676 then
(if i.val < 2674 then
(if i.val < 2673 then
[1, 2, 3, 0, 1, 1, 2, 2]
else
[1, 2, 3, 0, 1, 1, 2, 3])
else
(if i.val < 2675 then
[1, 2, 3, 0, 1, 2, 1, 0]
else
[1, 2, 3, 0, 1, 2, 1, 3]))
else
(if i.val < 2678 then
(if i.val < 2677 then
[1, 2, 3, 0, 1, 2, 2, 1]
else
[1, 2, 3, 0, 1, 2, 2, 3])
else
(if i.val < 2679 then
[1, 2, 3, 0, 1, 2, 3, 0]
else
[1, 2, 3, 0, 1, 2, 3, 3])))
else
(if i.val < 2684 then
(if i.val < 2682 then
(if i.val < 2681 then
[1, 2, 3, 0, 2, 1, 1, 2]
else
[1, 2, 3, 0, 2, 2, 1, 1])
else
(if i.val < 2683 then
[1, 2, 3, 0, 2, 3, 3, 2]
else
[1, 2, 3, 2, 1, 0, 3, 2]))
else
(if i.val < 2686 then
(if i.val < 2685 then
[1, 2, 3, 2, 2, 1, 1, 0]
else
[1, 2, 3, 2, 2, 1, 1, 3])
else
(if i.val < 2687 then
[1, 2, 3, 3, 0, 0, 1, 2]
else
[1, 2, 3, 3, 0, 0, 2, 3])))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row18_cosetWordsPart0021 : Fin 4320 → List (Fin 4) :=
  fun i => (if i.val < 2752 then
(if i.val < 2720 then
(if i.val < 2704 then
(if i.val < 2696 then
(if i.val < 2692 then
(if i.val < 2690 then
(if i.val < 2689 then
[1, 2, 3, 3, 0, 1, 1, 2]
else
[1, 2, 3, 3, 0, 1, 2, 2])
else
(if i.val < 2691 then
[1, 2, 3, 3, 0, 1, 2, 3]
else
[1, 2, 3, 3, 0, 2, 1, 3]))
else
(if i.val < 2694 then
(if i.val < 2693 then
[1, 2, 3, 3, 0, 2, 3, 3]
else
[1, 2, 3, 3, 2, 1, 0, 0])
else
(if i.val < 2695 then
[1, 2, 3, 3, 2, 1, 0, 3]
else
[1, 2, 3, 3, 2, 2, 1, 1])))
else
(if i.val < 2700 then
(if i.val < 2698 then
(if i.val < 2697 then
[1, 3, 0, 0, 1, 1, 2, 1]
else
[1, 3, 0, 0, 1, 1, 2, 2])
else
(if i.val < 2699 then
[1, 3, 0, 0, 1, 1, 2, 3]
else
[1, 3, 0, 0, 1, 2, 1, 1]))
else
(if i.val < 2702 then
(if i.val < 2701 then
[1, 3, 0, 0, 1, 2, 1, 3]
else
[1, 3, 0, 0, 1, 2, 2, 3])
else
(if i.val < 2703 then
[1, 3, 0, 0, 1, 2, 3, 0]
else
[1, 3, 0, 0, 1, 2, 3, 3]))))
else
(if i.val < 2712 then
(if i.val < 2708 then
(if i.val < 2706 then
(if i.val < 2705 then
[1, 3, 0, 0, 2, 2, 3, 2]
else
[1, 3, 0, 0, 2, 3, 2, 1])
else
(if i.val < 2707 then
[1, 3, 0, 0, 2, 3, 3, 2]
else
[1, 3, 0, 0, 3, 2, 1, 1]))
else
(if i.val < 2710 then
(if i.val < 2709 then
[1, 3, 0, 0, 3, 2, 2, 1]
else
[1, 3, 0, 1, 1, 0, 2, 1])
else
(if i.val < 2711 then
[1, 3, 0, 1, 1, 2, 1, 0]
else
[1, 3, 0, 1, 1, 2, 1, 1])))
else
(if i.val < 2716 then
(if i.val < 2714 then
(if i.val < 2713 then
[1, 3, 0, 1, 1, 2, 2, 1]
else
[1, 3, 0, 1, 1, 2, 2, 3])
else
(if i.val < 2715 then
[1, 3, 0, 1, 1, 2, 3, 0]
else
[1, 3, 0, 1, 2, 1, 0, 0]))
else
(if i.val < 2718 then
(if i.val < 2717 then
[1, 3, 0, 1, 2, 1, 1, 0]
else
[1, 3, 0, 1, 2, 1, 1, 2])
else
(if i.val < 2719 then
[1, 3, 0, 1, 2, 2, 1, 3]
else
[1, 3, 0, 1, 2, 3, 0, 0])))))
else
(if i.val < 2736 then
(if i.val < 2728 then
(if i.val < 2724 then
(if i.val < 2722 then
(if i.val < 2721 then
[1, 3, 0, 1, 2, 3, 0, 1]
else
[1, 3, 0, 1, 2, 3, 3, 0])
else
(if i.val < 2723 then
[1, 3, 0, 1, 2, 3, 3, 2]
else
[1, 3, 0, 2, 1, 1, 0, 2]))
else
(if i.val < 2726 then
(if i.val < 2725 then
[1, 3, 0, 2, 1, 1, 2, 3]
else
[1, 3, 0, 2, 2, 1, 0, 0])
else
(if i.val < 2727 then
[1, 3, 0, 2, 3, 3, 0, 2]
else
[1, 3, 0, 2, 3, 3, 2, 1])))
else
(if i.val < 2732 then
(if i.val < 2730 then
(if i.val < 2729 then
[1, 3, 2, 1, 0, 0, 3, 2]
else
[1, 3, 2, 1, 0, 3, 2, 2])
else
(if i.val < 2731 then
[1, 3, 2, 1, 1, 0, 0, 2]
else
[1, 3, 2, 1, 1, 0, 2, 3]))
else
(if i.val < 2734 then
(if i.val < 2733 then
[1, 3, 2, 1, 1, 2, 3, 3]
else
[1, 3, 2, 2, 1, 0, 0, 3])
else
(if i.val < 2735 then
[1, 3, 2, 2, 1, 0, 3, 2]
else
[1, 3, 2, 2, 1, 3, 0, 0]))))
else
(if i.val < 2744 then
(if i.val < 2740 then
(if i.val < 2738 then
(if i.val < 2737 then
[1, 3, 2, 2, 1, 3, 0, 1]
else
[1, 3, 2, 2, 3, 0, 1, 1])
else
(if i.val < 2739 then
[1, 3, 2, 2, 3, 0, 1, 2]
else
[1, 3, 3, 0, 0, 1, 2, 1]))
else
(if i.val < 2742 then
(if i.val < 2741 then
[1, 3, 3, 0, 0, 2, 1, 1]
else
[1, 3, 3, 0, 0, 2, 3, 3])
else
(if i.val < 2743 then
[1, 3, 3, 0, 1, 1, 2, 1]
else
[1, 3, 3, 0, 1, 2, 1, 1])))
else
(if i.val < 2748 then
(if i.val < 2746 then
(if i.val < 2745 then
[1, 3, 3, 0, 1, 2, 2, 1]
else
[1, 3, 3, 0, 1, 2, 3, 0])
else
(if i.val < 2747 then
[1, 3, 3, 0, 2, 1, 0, 0]
else
[1, 3, 3, 0, 2, 1, 1, 2]))
else
(if i.val < 2750 then
(if i.val < 2749 then
[1, 3, 3, 0, 2, 3, 3, 0]
else
[1, 3, 3, 0, 2, 3, 3, 2])
else
(if i.val < 2751 then
[1, 3, 3, 2, 1, 0, 0, 3]
else
[1, 3, 3, 2, 1, 1, 2, 3]))))))
else
(if i.val < 2784 then
(if i.val < 2768 then
(if i.val < 2760 then
(if i.val < 2756 then
(if i.val < 2754 then
(if i.val < 2753 then
[2, 1, 0, 0, 1, 2, 2, 1]
else
[2, 1, 0, 0, 1, 2, 3, 0])
else
(if i.val < 2755 then
[2, 1, 0, 0, 1, 3, 0, 2]
else
[2, 1, 0, 0, 3, 0, 1, 2]))
else
(if i.val < 2758 then
(if i.val < 2757 then
[2, 1, 0, 0, 3, 2, 2, 1]
else
[2, 1, 0, 0, 3, 2, 2, 3])
else
(if i.val < 2759 then
[2, 1, 0, 0, 3, 3, 2, 2]
else
[2, 1, 0, 3, 0, 0, 1, 2])))
else
(if i.val < 2764 then
(if i.val < 2762 then
(if i.val < 2761 then
[2, 1, 0, 3, 0, 1, 1, 2]
else
[2, 1, 0, 3, 0, 1, 2, 3])
else
(if i.val < 2763 then
[2, 1, 0, 3, 0, 2, 1, 0]
else
[2, 1, 0, 3, 0, 2, 1, 1]))
else
(if i.val < 2766 then
(if i.val < 2765 then
[2, 1, 0, 3, 0, 2, 2, 1]
else
[2, 1, 0, 3, 2, 1, 0, 0])
else
(if i.val < 2767 then
[2, 1, 0, 3, 2, 2, 1, 3]
else
[2, 1, 0, 3, 3, 0, 1, 2]))))
else
(if i.val < 2776 then
(if i.val < 2772 then
(if i.val < 2770 then
(if i.val < 2769 then
[2, 1, 0, 3, 3, 0, 2, 1]
else
[2, 1, 0, 3, 3, 2, 1, 0])
else
(if i.val < 2771 then
[2, 1, 0, 3, 3, 2, 1, 1]
else
[2, 1, 1, 0, 0, 2, 1, 3]))
else
(if i.val < 2774 then
(if i.val < 2773 then
[2, 1, 1, 0, 0, 2, 3, 0]
else
[2, 1, 1, 0, 0, 2, 3, 3])
else
(if i.val < 2775 then
[2, 1, 1, 0, 2, 1, 1, 2]
else
[2, 1, 1, 0, 2, 1, 1, 3])))
else
(if i.val < 2780 then
(if i.val < 2778 then
(if i.val < 2777 then
[2, 1, 1, 0, 2, 1, 3, 3]
else
[2, 1, 1, 0, 2, 3, 0, 0])
else
(if i.val < 2779 then
[2, 1, 1, 0, 2, 3, 0, 1]
else
[2, 1, 1, 0, 2, 3, 0, 2]))
else
(if i.val < 2782 then
(if i.val < 2781 then
[2, 1, 1, 0, 2, 3, 2, 1]
else
[2, 1, 1, 0, 2, 3, 3, 2])
else
(if i.val < 2783 then
[2, 1, 1, 0, 3, 0, 0, 2]
else
[2, 1, 1, 0, 3, 0, 2, 1])))))
else
(if i.val < 2800 then
(if i.val < 2792 then
(if i.val < 2788 then
(if i.val < 2786 then
(if i.val < 2785 then
[2, 1, 1, 0, 3, 0, 2, 2]
else
[2, 1, 1, 0, 3, 0, 2, 3])
else
(if i.val < 2787 then
[2, 1, 1, 0, 3, 2, 1, 1]
else
[2, 1, 1, 0, 3, 2, 2, 3]))
else
(if i.val < 2790 then
(if i.val < 2789 then
[2, 1, 1, 2, 3, 0, 0, 3]
else
[2, 1, 1, 2, 3, 0, 2, 2])
else
(if i.val < 2791 then
[2, 1, 1, 2, 3, 2, 1, 0]
else
[2, 1, 1, 2, 3, 3, 0, 1])))
else
(if i.val < 2796 then
(if i.val < 2794 then
(if i.val < 2793 then
[2, 1, 1, 2, 3, 3, 2, 1]
else
[2, 1, 1, 3, 0, 1, 2, 1])
else
(if i.val < 2795 then
[2, 1, 1, 3, 2, 2, 1, 0]
else
[2, 1, 1, 3, 2, 2, 1, 3]))
else
(if i.val < 2798 then
(if i.val < 2797 then
[2, 1, 1, 3, 2, 2, 3, 0]
else
[2, 1, 1, 3, 3, 0, 1, 2])
else
(if i.val < 2799 then
[2, 1, 3, 0, 0, 1, 2, 2]
else
[2, 1, 3, 0, 0, 3, 2, 2]))))
else
(if i.val < 2808 then
(if i.val < 2804 then
(if i.val < 2802 then
(if i.val < 2801 then
[2, 1, 3, 0, 1, 2, 2, 1]
else
[2, 1, 3, 0, 1, 2, 3, 0])
else
(if i.val < 2803 then
[2, 1, 3, 0, 1, 2, 3, 3]
else
[2, 1, 3, 2, 2, 1, 0, 0]))
else
(if i.val < 2806 then
(if i.val < 2805 then
[2, 1, 3, 2, 2, 3, 0, 1]
else
[2, 1, 3, 3, 0, 0, 1, 2])
else
(if i.val < 2807 then
[2, 1, 3, 3, 0, 0, 2, 3]
else
[2, 1, 3, 3, 0, 1, 2, 1])))
else
(if i.val < 2812 then
(if i.val < 2810 then
(if i.val < 2809 then
[2, 1, 3, 3, 0, 1, 2, 2]
else
[2, 1, 3, 3, 2, 1, 0, 3])
else
(if i.val < 2811 then
[2, 1, 3, 3, 2, 1, 1, 0]
else
[2, 1, 3, 3, 2, 2, 1, 1]))
else
(if i.val < 2814 then
(if i.val < 2813 then
[2, 2, 1, 0, 0, 1, 2, 3]
else
[2, 2, 1, 0, 0, 1, 3, 2])
else
(if i.val < 2815 then
[2, 2, 1, 0, 3, 0, 2, 1]
else
[2, 2, 1, 0, 3, 2, 1, 0])))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row18_cosetWordsPart0022 : Fin 4320 → List (Fin 4) :=
  fun i => (if i.val < 2880 then
(if i.val < 2848 then
(if i.val < 2832 then
(if i.val < 2824 then
(if i.val < 2820 then
(if i.val < 2818 then
(if i.val < 2817 then
[2, 2, 1, 0, 3, 2, 1, 1]
else
[2, 2, 1, 0, 3, 2, 2, 3])
else
(if i.val < 2819 then
[2, 2, 1, 1, 0, 3, 2, 1]
else
[2, 2, 1, 1, 3, 2, 1, 0]))
else
(if i.val < 2822 then
(if i.val < 2821 then
[2, 2, 1, 1, 3, 2, 2, 3]
else
[2, 2, 1, 3, 0, 0, 1, 2])
else
(if i.val < 2823 then
[2, 2, 1, 3, 0, 0, 3, 2]
else
[2, 2, 1, 3, 3, 0, 1, 2])))
else
(if i.val < 2828 then
(if i.val < 2826 then
(if i.val < 2825 then
[2, 2, 1, 3, 3, 2, 1, 0]
else
[2, 2, 1, 3, 3, 2, 1, 1])
else
(if i.val < 2827 then
[2, 2, 3, 0, 0, 1, 2, 2]
else
[2, 2, 3, 0, 0, 1, 2, 3]))
else
(if i.val < 2830 then
(if i.val < 2829 then
[2, 2, 3, 0, 0, 2, 1, 0]
else
[2, 2, 3, 0, 0, 2, 1, 1])
else
(if i.val < 2831 then
[2, 2, 3, 0, 0, 3, 2, 1]
else
[2, 2, 3, 0, 0, 3, 2, 2]))))
else
(if i.val < 2840 then
(if i.val < 2836 then
(if i.val < 2834 then
(if i.val < 2833 then
[2, 2, 3, 0, 1, 2, 1, 0]
else
[2, 2, 3, 0, 1, 2, 1, 3])
else
(if i.val < 2835 then
[2, 2, 3, 0, 1, 2, 3, 3]
else
[2, 2, 3, 0, 2, 1, 1, 2]))
else
(if i.val < 2838 then
(if i.val < 2837 then
[2, 2, 3, 0, 2, 2, 1, 1]
else
[2, 2, 3, 0, 2, 2, 1, 3])
else
(if i.val < 2839 then
[2, 2, 3, 0, 2, 3, 3, 0]
else
[2, 2, 3, 2, 2, 1, 0, 0])))
else
(if i.val < 2844 then
(if i.val < 2842 then
(if i.val < 2841 then
[2, 2, 3, 2, 2, 1, 1, 3]
else
[2, 2, 3, 2, 2, 3, 0, 0])
else
(if i.val < 2843 then
[2, 2, 3, 2, 2, 3, 0, 1]
else
[2, 2, 3, 3, 0, 1, 2, 1]))
else
(if i.val < 2846 then
(if i.val < 2845 then
[2, 3, 0, 0, 1, 1, 2, 1]
else
[2, 3, 0, 0, 1, 1, 2, 2])
else
(if i.val < 2847 then
[2, 3, 0, 0, 1, 1, 2, 3]
else
[2, 3, 0, 0, 1, 2, 2, 1])))))
else
(if i.val < 2864 then
(if i.val < 2856 then
(if i.val < 2852 then
(if i.val < 2850 then
(if i.val < 2849 then
[2, 3, 0, 0, 1, 2, 2, 3]
else
[2, 3, 0, 0, 1, 2, 3, 0])
else
(if i.val < 2851 then
[2, 3, 0, 0, 2, 3, 3, 2]
else
[2, 3, 0, 0, 3, 2, 1, 0]))
else
(if i.val < 2854 then
(if i.val < 2853 then
[2, 3, 0, 0, 3, 2, 1, 1]
else
[2, 3, 0, 0, 3, 2, 2, 1])
else
(if i.val < 2855 then
[2, 3, 0, 1, 1, 0, 2, 1]
else
[2, 3, 0, 1, 1, 0, 3, 2])))
else
(if i.val < 2860 then
(if i.val < 2858 then
(if i.val < 2857 then
[2, 3, 0, 1, 1, 2, 1, 0]
else
[2, 3, 0, 1, 1, 2, 1, 1])
else
(if i.val < 2859 then
[2, 3, 0, 1, 1, 2, 2, 1]
else
[2, 3, 0, 1, 1, 2, 3, 0]))
else
(if i.val < 2862 then
(if i.val < 2861 then
[2, 3, 0, 1, 2, 1, 1, 3]
else
[2, 3, 0, 1, 2, 1, 3, 0])
else
(if i.val < 2863 then
[2, 3, 0, 1, 2, 1, 3, 3]
else
[2, 3, 0, 1, 2, 2, 1, 3]))))
else
(if i.val < 2872 then
(if i.val < 2868 then
(if i.val < 2866 then
(if i.val < 2865 then
[2, 3, 0, 1, 2, 2, 3, 0]
else
[2, 3, 0, 1, 2, 3, 0, 1])
else
(if i.val < 2867 then
[2, 3, 0, 1, 2, 3, 3, 0]
else
[2, 3, 0, 1, 2, 3, 3, 2]))
else
(if i.val < 2870 then
(if i.val < 2869 then
[2, 3, 0, 2, 1, 1, 0, 2]
else
[2, 3, 0, 2, 1, 1, 2, 3])
else
(if i.val < 2871 then
[2, 3, 0, 2, 1, 3, 3, 0]
else
[2, 3, 0, 2, 2, 1, 3, 3])))
else
(if i.val < 2876 then
(if i.val < 2874 then
(if i.val < 2873 then
[2, 3, 0, 2, 2, 3, 3, 0]
else
[2, 3, 0, 2, 3, 3, 0, 2])
else
(if i.val < 2875 then
[2, 3, 0, 2, 3, 3, 2, 1]
else
[2, 3, 2, 1, 0, 3, 2, 1]))
else
(if i.val < 2878 then
(if i.val < 2877 then
[2, 3, 2, 1, 0, 3, 2, 2]
else
[2, 3, 2, 1, 1, 0, 3, 2])
else
(if i.val < 2879 then
[2, 3, 2, 1, 1, 0, 3, 3]
else
[2, 3, 2, 2, 1, 0, 3, 2]))))))
else
(if i.val < 2912 then
(if i.val < 2896 then
(if i.val < 2888 then
(if i.val < 2884 then
(if i.val < 2882 then
(if i.val < 2881 then
[2, 3, 2, 2, 1, 1, 0, 0]
else
[2, 3, 2, 2, 1, 3, 0, 0])
else
(if i.val < 2883 then
[2, 3, 2, 2, 1, 3, 0, 1]
else
[2, 3, 2, 2, 1, 3, 2, 2]))
else
(if i.val < 2886 then
(if i.val < 2885 then
[2, 3, 2, 2, 3, 0, 1, 1]
else
[2, 3, 2, 2, 3, 0, 1, 2])
else
(if i.val < 2887 then
[2, 3, 3, 0, 0, 2, 1, 3]
else
[2, 3, 3, 0, 0, 2, 3, 3])))
else
(if i.val < 2892 then
(if i.val < 2890 then
(if i.val < 2889 then
[2, 3, 3, 0, 1, 1, 0, 2]
else
[2, 3, 3, 0, 1, 2, 1, 0])
else
(if i.val < 2891 then
[2, 3, 3, 0, 1, 2, 1, 1]
else
[2, 3, 3, 0, 1, 2, 1, 3]))
else
(if i.val < 2894 then
(if i.val < 2893 then
[2, 3, 3, 0, 1, 2, 3, 3]
else
[2, 3, 3, 0, 2, 1, 0, 0])
else
(if i.val < 2895 then
[2, 3, 3, 0, 2, 1, 3, 3]
else
[2, 3, 3, 0, 2, 3, 3, 2]))))
else
(if i.val < 2904 then
(if i.val < 2900 then
(if i.val < 2898 then
(if i.val < 2897 then
[2, 3, 3, 2, 1, 0, 0, 3]
else
[3, 0, 0, 1, 1, 2, 1, 1])
else
(if i.val < 2899 then
[3, 0, 0, 1, 1, 2, 1, 3]
else
[3, 0, 0, 1, 1, 2, 2, 1]))
else
(if i.val < 2902 then
(if i.val < 2901 then
[3, 0, 0, 1, 1, 2, 3, 0]
else
[3, 0, 0, 1, 2, 1, 1, 3])
else
(if i.val < 2903 then
[3, 0, 0, 1, 2, 1, 3, 3]
else
[3, 0, 0, 1, 2, 2, 1, 3])))
else
(if i.val < 2908 then
(if i.val < 2906 then
(if i.val < 2905 then
[3, 0, 0, 1, 2, 3, 0, 1]
else
[3, 0, 0, 1, 2, 3, 0, 2])
else
(if i.val < 2907 then
[3, 0, 0, 1, 2, 3, 3, 2]
else
[3, 0, 0, 2, 1, 1, 0, 2]))
else
(if i.val < 2910 then
(if i.val < 2909 then
[3, 0, 0, 2, 1, 1, 2, 3]
else
[3, 0, 0, 2, 2, 1, 0, 0])
else
(if i.val < 2911 then
[3, 0, 0, 2, 2, 3, 2, 1]
else
[3, 0, 0, 2, 2, 3, 2, 2])))))
else
(if i.val < 2928 then
(if i.val < 2920 then
(if i.val < 2916 then
(if i.val < 2914 then
(if i.val < 2913 then
[3, 0, 0, 2, 3, 2, 1, 0]
else
[3, 0, 0, 2, 3, 2, 1, 1])
else
(if i.val < 2915 then
[3, 0, 0, 2, 3, 3, 2, 1]
else
[3, 0, 0, 3, 2, 1, 0, 0]))
else
(if i.val < 2918 then
(if i.val < 2917 then
[3, 0, 0, 3, 2, 1, 1, 0]
else
[3, 0, 0, 3, 2, 1, 1, 2])
else
(if i.val < 2919 then
[3, 0, 0, 3, 2, 2, 1, 0]
else
[3, 0, 0, 3, 2, 2, 1, 3])))
else
(if i.val < 2924 then
(if i.val < 2922 then
(if i.val < 2921 then
[3, 0, 1, 1, 0, 2, 3, 3]
else
[3, 0, 1, 1, 0, 3, 2, 1])
else
(if i.val < 2923 then
[3, 0, 1, 1, 2, 1, 0, 3]
else
[3, 0, 1, 1, 2, 1, 1, 0]))
else
(if i.val < 2926 then
(if i.val < 2925 then
[3, 0, 1, 1, 2, 1, 1, 2]
else
[3, 0, 1, 1, 2, 2, 1, 1])
else
(if i.val < 2927 then
[3, 0, 1, 1, 2, 2, 3, 0]
else
[3, 0, 1, 1, 2, 3, 0, 1]))))
else
(if i.val < 2936 then
(if i.val < 2932 then
(if i.val < 2930 then
(if i.val < 2929 then
[3, 0, 1, 1, 2, 3, 3, 0]
else
[3, 0, 1, 1, 2, 3, 3, 2])
else
(if i.val < 2931 then
[3, 0, 1, 2, 1, 0, 0, 3]
else
[3, 0, 1, 2, 1, 0, 3, 0]))
else
(if i.val < 2934 then
(if i.val < 2933 then
[3, 0, 1, 2, 1, 1, 0, 2]
else
[3, 0, 1, 2, 1, 1, 0, 3])
else
(if i.val < 2935 then
[3, 0, 1, 2, 1, 1, 2, 3]
else
[3, 0, 1, 2, 1, 1, 3, 0])))
else
(if i.val < 2940 then
(if i.val < 2938 then
(if i.val < 2937 then
[3, 0, 1, 2, 1, 1, 3, 3]
else
[3, 0, 1, 2, 1, 3, 0, 0])
else
(if i.val < 2939 then
[3, 0, 1, 2, 1, 3, 0, 1]
else
[3, 0, 1, 2, 1, 3, 3, 0]))
else
(if i.val < 2942 then
(if i.val < 2941 then
[3, 0, 1, 2, 1, 3, 3, 2]
else
[3, 0, 1, 2, 2, 1, 3, 3])
else
(if i.val < 2943 then
[3, 0, 1, 2, 2, 3, 0, 0]
else
[3, 0, 1, 2, 2, 3, 3, 0])))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row18_cosetWordsPart0023 : Fin 4320 → List (Fin 4) :=
  fun i => (if i.val < 3008 then
(if i.val < 2976 then
(if i.val < 2960 then
(if i.val < 2952 then
(if i.val < 2948 then
(if i.val < 2946 then
(if i.val < 2945 then
[3, 0, 1, 2, 3, 0, 0, 3]
else
[3, 0, 1, 2, 3, 0, 1, 1])
else
(if i.val < 2947 then
[3, 0, 1, 2, 3, 0, 1, 2]
else
[3, 0, 1, 2, 3, 3, 0, 1]))
else
(if i.val < 2950 then
(if i.val < 2949 then
[3, 0, 1, 2, 3, 3, 0, 2]
else
[3, 0, 2, 1, 0, 3, 3, 2])
else
(if i.val < 2951 then
[3, 0, 2, 1, 1, 0, 2, 1]
else
[3, 0, 2, 1, 1, 0, 3, 2])))
else
(if i.val < 2956 then
(if i.val < 2954 then
(if i.val < 2953 then
[3, 0, 2, 1, 1, 2, 3, 0]
else
[3, 0, 2, 1, 1, 2, 3, 3])
else
(if i.val < 2955 then
[3, 0, 2, 1, 1, 3, 2, 2]
else
[3, 0, 2, 1, 3, 3, 0, 1]))
else
(if i.val < 2958 then
(if i.val < 2957 then
[3, 0, 2, 1, 3, 3, 0, 2]
else
[3, 0, 2, 1, 3, 3, 2, 1])
else
(if i.val < 2959 then
[3, 0, 2, 1, 3, 3, 2, 2]
else
[3, 0, 2, 2, 1, 0, 3, 3]))))
else
(if i.val < 2968 then
(if i.val < 2964 then
(if i.val < 2962 then
(if i.val < 2961 then
[3, 0, 2, 2, 1, 1, 3, 0]
else
[3, 0, 2, 2, 1, 3, 3, 2])
else
(if i.val < 2963 then
[3, 0, 2, 3, 3, 0, 2, 1]
else
[3, 0, 2, 3, 3, 2, 1, 0]))
else
(if i.val < 2966 then
(if i.val < 2965 then
[3, 0, 2, 3, 3, 2, 1, 1]
else
[3, 2, 1, 0, 0, 1, 2, 2])
else
(if i.val < 2967 then
[3, 2, 1, 0, 0, 3, 2, 1]
else
[3, 2, 1, 0, 0, 3, 2, 2])))
else
(if i.val < 2972 then
(if i.val < 2970 then
(if i.val < 2969 then
[3, 2, 1, 0, 3, 2, 1, 0]
else
[3, 2, 1, 0, 3, 2, 1, 1])
else
(if i.val < 2971 then
[3, 2, 1, 0, 3, 2, 2, 1]
else
[3, 2, 1, 0, 3, 2, 2, 3]))
else
(if i.val < 2974 then
(if i.val < 2973 then
[3, 2, 1, 0, 3, 3, 0, 1]
else
[3, 2, 1, 1, 0, 0, 2, 3])
else
(if i.val < 2975 then
[3, 2, 1, 1, 0, 0, 3, 2]
else
[3, 2, 1, 1, 0, 2, 3, 2])))))
else
(if i.val < 2992 then
(if i.val < 2984 then
(if i.val < 2980 then
(if i.val < 2978 then
(if i.val < 2977 then
[3, 2, 1, 1, 0, 2, 3, 3]
else
[3, 2, 1, 1, 0, 3, 2, 1])
else
(if i.val < 2979 then
[3, 2, 1, 1, 2, 3, 0, 1]
else
[3, 2, 2, 1, 0, 0, 1, 2]))
else
(if i.val < 2982 then
(if i.val < 2981 then
[3, 2, 2, 1, 0, 0, 1, 3]
else
[3, 2, 2, 1, 0, 0, 3, 2])
else
(if i.val < 2983 then
[3, 2, 2, 1, 0, 3, 2, 1]
else
[3, 2, 2, 1, 0, 3, 2, 2])))
else
(if i.val < 2988 then
(if i.val < 2986 then
(if i.val < 2985 then
[3, 2, 2, 1, 1, 3, 0, 0]
else
[3, 2, 2, 1, 3, 0, 1, 1])
else
(if i.val < 2987 then
[3, 2, 2, 1, 3, 0, 1, 2]
else
[3, 2, 2, 1, 3, 2, 2, 3]))
else
(if i.val < 2990 then
(if i.val < 2989 then
[3, 2, 2, 3, 0, 0, 1, 2]
else
[3, 2, 2, 3, 0, 0, 3, 2])
else
(if i.val < 2991 then
[3, 3, 0, 0, 1, 2, 3, 0]
else
[3, 3, 0, 0, 2, 1, 0, 0]))))
else
(if i.val < 3000 then
(if i.val < 2996 then
(if i.val < 2994 then
(if i.val < 2993 then
[3, 3, 0, 0, 2, 3, 3, 2]
else
[3, 3, 0, 1, 1, 0, 2, 1])
else
(if i.val < 2995 then
[3, 3, 0, 1, 1, 0, 2, 3]
else
[3, 3, 0, 1, 1, 0, 3, 2]))
else
(if i.val < 2998 then
(if i.val < 2997 then
[3, 3, 0, 1, 1, 2, 3, 0]
else
[3, 3, 0, 1, 2, 1, 0, 0])
else
(if i.val < 2999 then
[3, 3, 0, 1, 2, 1, 1, 0]
else
[3, 3, 0, 1, 2, 1, 1, 3])))
else
(if i.val < 3004 then
(if i.val < 3002 then
(if i.val < 3001 then
[3, 3, 0, 1, 2, 2, 1, 0]
else
[3, 3, 0, 1, 2, 2, 3, 3])
else
(if i.val < 3003 then
[3, 3, 0, 1, 2, 3, 0, 0]
else
[3, 3, 0, 1, 2, 3, 0, 1]))
else
(if i.val < 3006 then
(if i.val < 3005 then
[3, 3, 0, 1, 2, 3, 3, 2]
else
[3, 3, 0, 2, 1, 0, 3, 3])
else
(if i.val < 3007 then
[3, 3, 0, 2, 1, 1, 2, 3]
else
[3, 3, 0, 2, 2, 1, 3, 3]))))))
else
(if i.val < 3040 then
(if i.val < 3024 then
(if i.val < 3016 then
(if i.val < 3012 then
(if i.val < 3010 then
(if i.val < 3009 then
[3, 3, 0, 2, 3, 3, 0, 2]
else
[3, 3, 0, 2, 3, 3, 2, 1])
else
(if i.val < 3011 then
[3, 3, 2, 1, 0, 3, 2, 2]
else
[3, 3, 2, 1, 1, 0, 3, 3]))
else
(if i.val < 3014 then
(if i.val < 3013 then
[3, 3, 2, 1, 1, 2, 3, 3]
else
[3, 3, 2, 2, 1, 0, 3, 2])
else
(if i.val < 3015 then
[0, 0, 1, 0, 0, 1, 2, 1, 0]
else
[0, 0, 1, 0, 0, 1, 2, 1, 1])))
else
(if i.val < 3020 then
(if i.val < 3018 then
(if i.val < 3017 then
[0, 0, 1, 0, 0, 1, 2, 1, 3]
else
[0, 0, 1, 0, 0, 1, 3, 0, 2])
else
(if i.val < 3019 then
[0, 0, 1, 0, 0, 1, 3, 2, 1]
else
[0, 0, 1, 0, 0, 2, 1, 1, 2]))
else
(if i.val < 3022 then
(if i.val < 3021 then
[0, 0, 1, 0, 0, 2, 1, 1, 3]
else
[0, 0, 1, 0, 0, 2, 2, 1, 3])
else
(if i.val < 3023 then
[0, 0, 1, 0, 0, 2, 3, 2, 2]
else
[0, 0, 1, 0, 0, 2, 3, 3, 2]))))
else
(if i.val < 3032 then
(if i.val < 3028 then
(if i.val < 3026 then
(if i.val < 3025 then
[0, 0, 1, 0, 0, 3, 0, 1, 2]
else
[0, 0, 1, 0, 0, 3, 3, 0, 2])
else
(if i.val < 3027 then
[0, 0, 1, 0, 2, 1, 0, 0, 3]
else
[0, 0, 1, 0, 2, 1, 1, 3, 3]))
else
(if i.val < 3030 then
(if i.val < 3029 then
[0, 0, 1, 0, 2, 2, 1, 1, 0]
else
[0, 0, 1, 0, 2, 2, 3, 0, 2])
else
(if i.val < 3031 then
[0, 0, 1, 0, 2, 2, 3, 2, 1]
else
[0, 0, 1, 0, 2, 2, 3, 3, 0])))
else
(if i.val < 3036 then
(if i.val < 3034 then
(if i.val < 3033 then
[0, 0, 1, 0, 2, 2, 3, 3, 2]
else
[0, 0, 1, 0, 2, 3, 0, 0, 3])
else
(if i.val < 3035 then
[0, 0, 1, 0, 2, 3, 2, 1, 1]
else
[0, 0, 1, 0, 2, 3, 3, 2, 1]))
else
(if i.val < 3038 then
(if i.val < 3037 then
[0, 0, 1, 0, 3, 0, 0, 2, 1]
else
[0, 0, 1, 0, 3, 0, 1, 1, 2])
else
(if i.val < 3039 then
[0, 0, 1, 1, 0, 0, 2, 1, 3]
else
[0, 0, 1, 1, 0, 0, 2, 3, 0])))))
else
(if i.val < 3056 then
(if i.val < 3048 then
(if i.val < 3044 then
(if i.val < 3042 then
(if i.val < 3041 then
[0, 0, 1, 1, 0, 2, 1, 0, 0]
else
[0, 0, 1, 1, 0, 2, 1, 1, 2])
else
(if i.val < 3043 then
[0, 0, 1, 1, 0, 2, 2, 1, 3]
else
[0, 0, 1, 1, 0, 2, 3, 0, 1]))
else
(if i.val < 3046 then
(if i.val < 3045 then
[0, 0, 1, 1, 0, 2, 3, 0, 2]
else
[0, 0, 1, 1, 0, 2, 3, 2, 1])
else
(if i.val < 3047 then
[0, 0, 1, 1, 0, 3, 0, 2, 1]
else
[0, 0, 1, 1, 0, 3, 0, 2, 2])))
else
(if i.val < 3052 then
(if i.val < 3050 then
(if i.val < 3049 then
[0, 0, 1, 1, 0, 3, 0, 2, 3]
else
[0, 0, 1, 1, 0, 3, 2, 1, 0])
else
(if i.val < 3051 then
[0, 0, 1, 1, 0, 3, 2, 2, 1]
else
[0, 0, 1, 1, 0, 3, 2, 2, 3]))
else
(if i.val < 3054 then
(if i.val < 3053 then
[0, 0, 1, 1, 2, 1, 0, 3, 0]
else
[0, 0, 1, 1, 2, 1, 0, 3, 3])
else
(if i.val < 3055 then
[0, 0, 1, 1, 2, 1, 3, 0, 0]
else
[0, 0, 1, 1, 2, 2, 3, 2, 1]))))
else
(if i.val < 3064 then
(if i.val < 3060 then
(if i.val < 3058 then
(if i.val < 3057 then
[0, 0, 1, 1, 2, 3, 0, 0, 3]
else
[0, 0, 1, 1, 2, 3, 2, 1, 0])
else
(if i.val < 3059 then
[0, 0, 1, 1, 3, 0, 1, 2, 1]
else
[0, 0, 1, 1, 3, 0, 2, 1, 1]))
else
(if i.val < 3062 then
(if i.val < 3061 then
[0, 0, 1, 1, 3, 2, 1, 1, 0]
else
[0, 0, 1, 1, 3, 2, 1, 1, 2])
else
(if i.val < 3063 then
[0, 0, 1, 1, 3, 2, 2, 1, 0]
else
[0, 0, 1, 1, 3, 2, 2, 3, 0])))
else
(if i.val < 3068 then
(if i.val < 3066 then
(if i.val < 3065 then
[0, 0, 1, 2, 1, 0, 3, 0, 0]
else
[0, 0, 1, 2, 1, 0, 3, 0, 1])
else
(if i.val < 3067 then
[0, 0, 1, 2, 1, 1, 0, 0, 2]
else
[0, 0, 1, 2, 1, 1, 0, 3, 2]))
else
(if i.val < 3070 then
(if i.val < 3069 then
[0, 0, 1, 2, 1, 1, 2, 3, 0]
else
[0, 0, 1, 2, 1, 1, 3, 0, 1])
else
(if i.val < 3071 then
[0, 0, 1, 2, 1, 3, 0, 1, 1]
else
[0, 0, 1, 2, 1, 3, 0, 1, 2])))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row18_cosetWordsPart0024 : Fin 4320 → List (Fin 4) :=
  fun i => (if i.val < 3136 then
(if i.val < 3104 then
(if i.val < 3088 then
(if i.val < 3080 then
(if i.val < 3076 then
(if i.val < 3074 then
(if i.val < 3073 then
[0, 0, 1, 2, 1, 3, 3, 0, 1]
else
[0, 0, 1, 2, 1, 3, 3, 2, 2])
else
(if i.val < 3075 then
[0, 0, 1, 2, 2, 1, 0, 0, 3]
else
[0, 0, 1, 2, 2, 1, 0, 3, 2]))
else
(if i.val < 3078 then
(if i.val < 3077 then
[0, 0, 1, 2, 2, 1, 3, 0, 0]
else
[0, 0, 1, 2, 2, 1, 3, 0, 1])
else
(if i.val < 3079 then
[0, 0, 1, 2, 2, 3, 0, 0, 3]
else
[0, 0, 1, 2, 2, 3, 0, 2, 2])))
else
(if i.val < 3084 then
(if i.val < 3082 then
(if i.val < 3081 then
[0, 0, 1, 2, 2, 3, 2, 2, 1]
else
[0, 0, 1, 2, 3, 0, 1, 1, 2])
else
(if i.val < 3083 then
[0, 0, 1, 2, 3, 0, 1, 2, 1]
else
[0, 0, 1, 2, 3, 0, 1, 2, 2]))
else
(if i.val < 3086 then
(if i.val < 3085 then
[0, 0, 1, 2, 3, 2, 2, 1, 0]
else
[0, 0, 1, 2, 3, 2, 2, 1, 3])
else
(if i.val < 3087 then
[0, 0, 1, 2, 3, 3, 0, 0, 2]
else
[0, 0, 1, 2, 3, 3, 0, 1, 2]))))
else
(if i.val < 3096 then
(if i.val < 3092 then
(if i.val < 3090 then
(if i.val < 3089 then
[0, 0, 1, 2, 3, 3, 0, 2, 2]
else
[0, 0, 1, 2, 3, 3, 0, 2, 3])
else
(if i.val < 3091 then
[0, 0, 1, 2, 3, 3, 2, 1, 1]
else
[0, 0, 1, 2, 3, 3, 2, 2, 1]))
else
(if i.val < 3094 then
(if i.val < 3093 then
[0, 0, 1, 3, 0, 0, 1, 1, 2]
else
[0, 0, 1, 3, 0, 0, 1, 2, 1])
else
(if i.val < 3095 then
[0, 0, 1, 3, 0, 0, 1, 2, 2]
else
[0, 0, 1, 3, 0, 0, 3, 2, 1])))
else
(if i.val < 3100 then
(if i.val < 3098 then
(if i.val < 3097 then
[0, 0, 1, 3, 0, 0, 3, 2, 2]
else
[0, 0, 1, 3, 0, 2, 2, 1, 1])
else
(if i.val < 3099 then
[0, 0, 1, 3, 2, 1, 0, 3, 2]
else
[0, 0, 1, 3, 2, 1, 1, 2, 3]))
else
(if i.val < 3102 then
(if i.val < 3101 then
[0, 0, 1, 3, 3, 0, 0, 2, 3]
else
[0, 0, 1, 3, 3, 0, 1, 2, 1])
else
(if i.val < 3103 then
[0, 0, 1, 3, 3, 0, 1, 2, 3]
else
[0, 0, 1, 3, 3, 0, 2, 1, 1])))))
else
(if i.val < 3120 then
(if i.val < 3112 then
(if i.val < 3108 then
(if i.val < 3106 then
(if i.val < 3105 then
[0, 0, 1, 3, 3, 2, 1, 0, 3]
else
[0, 0, 1, 3, 3, 2, 1, 1, 0])
else
(if i.val < 3107 then
[0, 0, 2, 1, 0, 0, 1, 2, 2]
else
[0, 0, 2, 1, 0, 0, 1, 3, 2]))
else
(if i.val < 3110 then
(if i.val < 3109 then
[0, 0, 2, 1, 0, 0, 3, 2, 1]
else
[0, 0, 2, 1, 0, 0, 3, 3, 2])
else
(if i.val < 3111 then
[0, 0, 2, 1, 0, 3, 2, 1, 0]
else
[0, 0, 2, 1, 0, 3, 2, 1, 1])))
else
(if i.val < 3116 then
(if i.val < 3114 then
(if i.val < 3113 then
[0, 0, 2, 1, 0, 3, 2, 2, 3]
else
[0, 0, 2, 1, 1, 0, 0, 2, 1])
else
(if i.val < 3115 then
[0, 0, 2, 1, 1, 0, 0, 2, 3]
else
[0, 0, 2, 1, 1, 0, 2, 1, 1]))
else
(if i.val < 3118 then
(if i.val < 3117 then
[0, 0, 2, 1, 1, 0, 2, 1, 3]
else
[0, 0, 2, 1, 1, 0, 3, 2, 1])
else
(if i.val < 3119 then
[0, 0, 2, 1, 1, 2, 3, 0, 0]
else
[0, 0, 2, 1, 1, 2, 3, 0, 1]))))
else
(if i.val < 3128 then
(if i.val < 3124 then
(if i.val < 3122 then
(if i.val < 3121 then
[0, 0, 2, 1, 1, 2, 3, 0, 2]
else
[0, 0, 2, 1, 1, 3, 0, 2, 2])
else
(if i.val < 3123 then
[0, 0, 2, 1, 1, 3, 2, 2, 1]
else
[0, 0, 2, 1, 1, 3, 2, 2, 3]))
else
(if i.val < 3126 then
(if i.val < 3125 then
[0, 0, 2, 1, 3, 0, 0, 1, 2]
else
[0, 0, 2, 1, 3, 0, 0, 3, 2])
else
(if i.val < 3127 then
[0, 0, 2, 1, 3, 3, 0, 1, 2]
else
[0, 0, 2, 1, 3, 3, 0, 2, 2])))
else
(if i.val < 3132 then
(if i.val < 3130 then
(if i.val < 3129 then
[0, 0, 2, 1, 3, 3, 0, 2, 3]
else
[0, 0, 2, 1, 3, 3, 2, 1, 0])
else
(if i.val < 3131 then
[0, 0, 2, 1, 3, 3, 2, 2, 1]
else
[0, 0, 2, 2, 1, 0, 3, 2, 2]))
else
(if i.val < 3134 then
(if i.val < 3133 then
[0, 0, 2, 2, 1, 3, 2, 2, 3]
else
[0, 0, 2, 2, 3, 0, 0, 2, 2])
else
(if i.val < 3135 then
[0, 0, 2, 2, 3, 0, 0, 3, 2]
else
[0, 0, 2, 2, 3, 0, 1, 2, 1]))))))
else
(if i.val < 3168 then
(if i.val < 3152 then
(if i.val < 3144 then
(if i.val < 3140 then
(if i.val < 3138 then
(if i.val < 3137 then
[0, 0, 2, 2, 3, 0, 1, 2, 3]
else
[0, 0, 2, 2, 3, 0, 2, 1, 0])
else
(if i.val < 3139 then
[0, 0, 2, 2, 3, 0, 2, 2, 1]
else
[0, 0, 2, 2, 3, 2, 1, 0, 3]))
else
(if i.val < 3142 then
(if i.val < 3141 then
[0, 0, 2, 2, 3, 2, 2, 1, 0]
else
[0, 0, 2, 2, 3, 2, 2, 1, 3])
else
(if i.val < 3143 then
[0, 0, 2, 3, 0, 0, 1, 1, 2]
else
[0, 0, 2, 3, 0, 0, 2, 1, 0])))
else
(if i.val < 3148 then
(if i.val < 3146 then
(if i.val < 3145 then
[0, 0, 2, 3, 0, 0, 2, 1, 1]
else
[0, 0, 2, 3, 0, 1, 2, 1, 3])
else
(if i.val < 3147 then
[0, 0, 2, 3, 0, 1, 2, 3, 0]
else
[0, 0, 2, 3, 0, 1, 2, 3, 3]))
else
(if i.val < 3150 then
(if i.val < 3149 then
[0, 0, 2, 3, 0, 2, 1, 0, 3]
else
[0, 0, 2, 3, 0, 2, 2, 1, 3])
else
(if i.val < 3151 then
[0, 0, 2, 3, 0, 2, 2, 3, 3]
else
[0, 0, 2, 3, 2, 1, 1, 0, 0]))))
else
(if i.val < 3160 then
(if i.val < 3156 then
(if i.val < 3154 then
(if i.val < 3153 then
[0, 0, 2, 3, 2, 2, 1, 0, 0]
else
[0, 0, 2, 3, 3, 0, 0, 2, 1])
else
(if i.val < 3155 then
[0, 0, 2, 3, 3, 0, 0, 2, 3]
else
[0, 0, 2, 3, 3, 0, 1, 2, 1]))
else
(if i.val < 3158 then
(if i.val < 3157 then
[0, 0, 2, 3, 3, 0, 2, 1, 3]
else
[0, 0, 2, 3, 3, 2, 1, 0, 0])
else
(if i.val < 3159 then
[0, 0, 2, 3, 3, 2, 1, 0, 3]
else
[0, 0, 3, 0, 0, 1, 1, 2, 3])))
else
(if i.val < 3164 then
(if i.val < 3162 then
(if i.val < 3161 then
[0, 0, 3, 0, 0, 1, 2, 1, 1]
else
[0, 0, 3, 0, 0, 1, 3, 2, 1])
else
(if i.val < 3163 then
[0, 0, 3, 0, 0, 1, 3, 2, 2]
else
[0, 0, 3, 0, 0, 2, 1, 0, 0]))
else
(if i.val < 3166 then
(if i.val < 3165 then
[0, 0, 3, 0, 0, 2, 2, 1, 3]
else
[0, 0, 3, 0, 0, 2, 3, 2, 1])
else
(if i.val < 3167 then
[0, 0, 3, 0, 0, 2, 3, 3, 2]
else
[0, 0, 3, 0, 0, 3, 2, 1, 0])))))
else
(if i.val < 3184 then
(if i.val < 3176 then
(if i.val < 3172 then
(if i.val < 3170 then
(if i.val < 3169 then
[0, 0, 3, 0, 0, 3, 2, 1, 1]
else
[0, 0, 3, 0, 1, 2, 1, 1, 0])
else
(if i.val < 3171 then
[0, 0, 3, 0, 1, 2, 1, 1, 3]
else
[0, 0, 3, 0, 1, 2, 1, 3, 3]))
else
(if i.val < 3174 then
(if i.val < 3173 then
[0, 0, 3, 0, 1, 2, 2, 3, 0]
else
[0, 0, 3, 0, 1, 2, 2, 3, 3])
else
(if i.val < 3175 then
[0, 0, 3, 0, 1, 2, 3, 0, 1]
else
[0, 0, 3, 0, 1, 2, 3, 3, 0])))
else
(if i.val < 3180 then
(if i.val < 3178 then
(if i.val < 3177 then
[0, 0, 3, 0, 2, 2, 1, 1, 0]
else
[0, 0, 3, 0, 2, 2, 3, 3, 0])
else
(if i.val < 3179 then
[0, 0, 3, 0, 2, 3, 3, 0, 2]
else
[0, 0, 3, 0, 2, 3, 3, 2, 1]))
else
(if i.val < 3182 then
(if i.val < 3181 then
[0, 0, 3, 2, 1, 0, 0, 3, 2]
else
[0, 0, 3, 2, 1, 0, 3, 2, 2])
else
(if i.val < 3183 then
[0, 0, 3, 2, 1, 1, 0, 2, 1]
else
[0, 0, 3, 2, 1, 1, 0, 3, 2]))))
else
(if i.val < 3192 then
(if i.val < 3188 then
(if i.val < 3186 then
(if i.val < 3185 then
[0, 0, 3, 2, 1, 1, 0, 3, 3]
else
[0, 0, 3, 2, 2, 1, 0, 0, 3])
else
(if i.val < 3187 then
[0, 0, 3, 2, 2, 1, 3, 0, 0]
else
[0, 0, 3, 2, 2, 1, 3, 0, 1]))
else
(if i.val < 3190 then
(if i.val < 3189 then
[0, 0, 3, 2, 2, 1, 3, 0, 2]
else
[0, 0, 3, 2, 2, 3, 0, 0, 3])
else
(if i.val < 3191 then
[0, 0, 3, 2, 2, 3, 0, 1, 2]
else
[0, 0, 3, 3, 0, 0, 2, 1, 3])))
else
(if i.val < 3196 then
(if i.val < 3194 then
(if i.val < 3193 then
[0, 0, 3, 3, 0, 1, 2, 1, 0]
else
[0, 0, 3, 3, 0, 1, 2, 1, 3])
else
(if i.val < 3195 then
[0, 0, 3, 3, 0, 1, 2, 2, 3]
else
[0, 0, 3, 3, 0, 1, 2, 3, 0]))
else
(if i.val < 3198 then
(if i.val < 3197 then
[0, 0, 3, 3, 0, 2, 3, 3, 2]
else
[0, 0, 3, 3, 2, 1, 0, 3, 3])
else
(if i.val < 3199 then
[0, 1, 0, 0, 1, 2, 1, 0, 0]
else
[0, 1, 0, 0, 1, 2, 1, 0, 3])))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row18_cosetWordsPart0025 : Fin 4320 → List (Fin 4) :=
  fun i => (if i.val < 3264 then
(if i.val < 3232 then
(if i.val < 3216 then
(if i.val < 3208 then
(if i.val < 3204 then
(if i.val < 3202 then
(if i.val < 3201 then
[0, 1, 0, 0, 1, 2, 1, 1, 2]
else
[0, 1, 0, 0, 1, 2, 2, 1, 0])
else
(if i.val < 3203 then
[0, 1, 0, 0, 1, 2, 2, 1, 3]
else
[0, 1, 0, 0, 1, 2, 3, 0, 0]))
else
(if i.val < 3206 then
(if i.val < 3205 then
[0, 1, 0, 0, 1, 2, 3, 0, 2]
else
[0, 1, 0, 0, 1, 2, 3, 3, 2])
else
(if i.val < 3207 then
[0, 1, 0, 0, 1, 3, 2, 2, 3]
else
[0, 1, 0, 0, 2, 1, 0, 3, 3])))
else
(if i.val < 3212 then
(if i.val < 3210 then
(if i.val < 3209 then
[0, 1, 0, 0, 2, 1, 1, 0, 2]
else
[0, 1, 0, 0, 2, 1, 1, 0, 3])
else
(if i.val < 3211 then
[0, 1, 0, 0, 2, 1, 1, 2, 3]
else
[0, 1, 0, 0, 2, 2, 1, 0, 0]))
else
(if i.val < 3214 then
(if i.val < 3213 then
[0, 1, 0, 0, 2, 3, 0, 0, 3]
else
[0, 1, 0, 0, 2, 3, 0, 1, 1])
else
(if i.val < 3215 then
[0, 1, 0, 0, 2, 3, 0, 2, 2]
else
[0, 1, 0, 0, 2, 3, 2, 2, 1]))))
else
(if i.val < 3224 then
(if i.val < 3220 then
(if i.val < 3218 then
(if i.val < 3217 then
[0, 1, 0, 0, 2, 3, 3, 2, 2]
else
[0, 1, 0, 0, 3, 0, 0, 3, 2])
else
(if i.val < 3219 then
[0, 1, 0, 0, 3, 3, 0, 2, 1]
else
[0, 1, 0, 0, 3, 3, 0, 2, 2]))
else
(if i.val < 3222 then
(if i.val < 3221 then
[0, 1, 0, 0, 3, 3, 0, 2, 3]
else
[0, 1, 0, 0, 3, 3, 2, 1, 0])
else
(if i.val < 3223 then
[0, 1, 0, 0, 3, 3, 2, 2, 1]
else
[0, 1, 0, 2, 1, 0, 0, 1, 2])))
else
(if i.val < 3228 then
(if i.val < 3226 then
(if i.val < 3225 then
[0, 1, 0, 2, 1, 0, 0, 1, 3]
else
[0, 1, 0, 2, 1, 0, 3, 3, 2])
else
(if i.val < 3227 then
[0, 1, 0, 2, 1, 1, 0, 0, 2]
else
[0, 1, 0, 2, 1, 1, 0, 2, 1]))
else
(if i.val < 3230 then
(if i.val < 3229 then
[0, 1, 0, 2, 1, 1, 0, 2, 3]
else
[0, 1, 0, 2, 1, 1, 2, 3, 0])
else
(if i.val < 3231 then
[0, 1, 0, 2, 1, 1, 2, 3, 3]
else
[0, 1, 0, 2, 1, 1, 3, 3, 2])))))
else
(if i.val < 3248 then
(if i.val < 3240 then
(if i.val < 3236 then
(if i.val < 3234 then
(if i.val < 3233 then
[0, 1, 0, 2, 1, 3, 3, 0, 1]
else
[0, 1, 0, 2, 1, 3, 3, 2, 1])
else
(if i.val < 3235 then
[0, 1, 0, 2, 1, 3, 3, 2, 2]
else
[0, 1, 0, 2, 2, 1, 0, 0, 3]))
else
(if i.val < 3238 then
(if i.val < 3237 then
[0, 1, 0, 2, 2, 1, 0, 3, 2]
else
[0, 1, 0, 2, 2, 1, 0, 3, 3])
else
(if i.val < 3239 then
[0, 1, 0, 2, 2, 1, 1, 3, 0]
else
[0, 1, 0, 2, 2, 1, 3, 0, 0])))
else
(if i.val < 3244 then
(if i.val < 3242 then
(if i.val < 3241 then
[0, 1, 0, 2, 2, 1, 3, 0, 1]
else
[0, 1, 0, 2, 2, 1, 3, 3, 0])
else
(if i.val < 3243 then
[0, 1, 0, 2, 2, 1, 3, 3, 2]
else
[0, 1, 0, 2, 2, 3, 0, 0, 3]))
else
(if i.val < 3246 then
(if i.val < 3245 then
[0, 1, 0, 2, 2, 3, 0, 1, 2]
else
[0, 1, 0, 2, 2, 3, 0, 2, 1])
else
(if i.val < 3247 then
[0, 1, 0, 2, 2, 3, 0, 2, 2]
else
[0, 1, 0, 2, 2, 3, 2, 2, 1]))))
else
(if i.val < 3256 then
(if i.val < 3252 then
(if i.val < 3250 then
(if i.val < 3249 then
[0, 1, 0, 2, 2, 3, 3, 0, 1]
else
[0, 1, 0, 2, 3, 0, 1, 2, 1])
else
(if i.val < 3251 then
[0, 1, 0, 2, 3, 0, 1, 2, 2]
else
[0, 1, 0, 2, 3, 0, 1, 2, 3]))
else
(if i.val < 3254 then
(if i.val < 3253 then
[0, 1, 0, 2, 3, 0, 2, 1, 1]
else
[0, 1, 0, 2, 3, 2, 1, 1, 0])
else
(if i.val < 3255 then
[0, 1, 0, 2, 3, 2, 2, 3, 0]
else
[0, 1, 0, 2, 3, 3, 0, 1, 2])))
else
(if i.val < 3260 then
(if i.val < 3258 then
(if i.val < 3257 then
[0, 1, 0, 2, 3, 3, 0, 2, 1]
else
[0, 1, 0, 2, 3, 3, 0, 2, 3])
else
(if i.val < 3259 then
[0, 1, 0, 2, 3, 3, 2, 1, 1]
else
[0, 1, 0, 3, 0, 0, 1, 1, 2]))
else
(if i.val < 3262 then
(if i.val < 3261 then
[0, 1, 0, 3, 0, 0, 2, 1, 1]
else
[0, 1, 0, 3, 0, 0, 2, 3, 2])
else
(if i.val < 3263 then
[0, 1, 0, 3, 0, 0, 3, 2, 2]
else
[0, 1, 0, 3, 2, 1, 0, 3, 2]))))))
else
(if i.val < 3296 then
(if i.val < 3280 then
(if i.val < 3272 then
(if i.val < 3268 then
(if i.val < 3266 then
(if i.val < 3265 then
[0, 1, 0, 3, 2, 1, 1, 2, 3]
else
[0, 1, 0, 3, 2, 2, 3, 0, 0])
else
(if i.val < 3267 then
[0, 1, 0, 3, 3, 0, 1, 2, 1]
else
[0, 1, 0, 3, 3, 2, 1, 0, 3]))
else
(if i.val < 3270 then
(if i.val < 3269 then
[0, 1, 0, 3, 3, 2, 1, 1, 2]
else
[0, 1, 0, 3, 3, 2, 2, 1, 1])
else
(if i.val < 3271 then
[0, 1, 1, 0, 0, 2, 1, 0, 0]
else
[0, 1, 1, 0, 0, 2, 1, 3, 3])))
else
(if i.val < 3276 then
(if i.val < 3274 then
(if i.val < 3273 then
[0, 1, 1, 0, 0, 2, 3, 0, 0]
else
[0, 1, 1, 0, 0, 2, 3, 0, 1])
else
(if i.val < 3275 then
[0, 1, 1, 0, 0, 2, 3, 3, 2]
else
[0, 1, 1, 0, 0, 3, 0, 1, 2]))
else
(if i.val < 3278 then
(if i.val < 3277 then
[0, 1, 1, 0, 2, 1, 0, 3, 3]
else
[0, 1, 1, 0, 2, 1, 1, 2, 3])
else
(if i.val < 3279 then
[0, 1, 1, 0, 2, 2, 3, 2, 1]
else
[0, 1, 1, 0, 2, 2, 3, 3, 2]))))
else
(if i.val < 3288 then
(if i.val < 3284 then
(if i.val < 3282 then
(if i.val < 3281 then
[0, 1, 1, 0, 2, 3, 0, 0, 3]
else
[0, 1, 1, 0, 2, 3, 0, 2, 1])
else
(if i.val < 3283 then
[0, 1, 1, 0, 2, 3, 0, 2, 3]
else
[0, 1, 1, 0, 2, 3, 2, 1, 1]))
else
(if i.val < 3286 then
(if i.val < 3285 then
[0, 1, 1, 0, 2, 3, 3, 2, 1]
else
[0, 1, 1, 0, 3, 0, 0, 2, 1])
else
(if i.val < 3287 then
[0, 1, 1, 0, 3, 0, 0, 3, 2]
else
[0, 1, 1, 0, 3, 0, 1, 2, 1])))
else
(if i.val < 3292 then
(if i.val < 3290 then
(if i.val < 3289 then
[0, 1, 1, 0, 3, 0, 2, 2, 1]
else
[0, 1, 1, 0, 3, 2, 1, 1, 0])
else
(if i.val < 3291 then
[0, 1, 1, 0, 3, 2, 1, 1, 2]
else
[0, 1, 1, 0, 3, 2, 2, 1, 0]))
else
(if i.val < 3294 then
(if i.val < 3293 then
[0, 1, 1, 0, 3, 2, 2, 1, 3]
else
[0, 1, 1, 0, 3, 3, 0, 1, 2])
else
(if i.val < 3295 then
[0, 1, 1, 0, 3, 3, 0, 2, 1]
else
[0, 1, 1, 0, 3, 3, 0, 2, 3])))))
else
(if i.val < 3312 then
(if i.val < 3304 then
(if i.val < 3300 then
(if i.val < 3298 then
(if i.val < 3297 then
[0, 1, 1, 2, 1, 0, 0, 1, 2]
else
[0, 1, 1, 2, 1, 0, 3, 0, 0])
else
(if i.val < 3299 then
[0, 1, 1, 2, 1, 0, 3, 0, 1]
else
[0, 1, 1, 2, 1, 0, 3, 3, 2]))
else
(if i.val < 3302 then
(if i.val < 3301 then
[0, 1, 1, 2, 1, 1, 0, 3, 2]
else
[0, 1, 1, 2, 1, 1, 0, 3, 3])
else
(if i.val < 3303 then
[0, 1, 1, 2, 1, 1, 3, 0, 0]
else
[0, 1, 1, 2, 1, 1, 3, 0, 1])))
else
(if i.val < 3308 then
(if i.val < 3306 then
(if i.val < 3305 then
[0, 1, 1, 2, 1, 3, 2, 2, 1]
else
[0, 1, 1, 2, 1, 3, 3, 0, 0])
else
(if i.val < 3307 then
[0, 1, 1, 2, 1, 3, 3, 0, 1]
else
[0, 1, 1, 2, 1, 3, 3, 2, 2]))
else
(if i.val < 3310 then
(if i.val < 3309 then
[0, 1, 1, 2, 2, 1, 0, 3, 3]
else
[0, 1, 1, 2, 2, 1, 3, 3, 2])
else
(if i.val < 3311 then
[0, 1, 1, 2, 2, 3, 2, 1, 0]
else
[0, 1, 1, 2, 2, 3, 2, 1, 1]))))
else
(if i.val < 3320 then
(if i.val < 3316 then
(if i.val < 3314 then
(if i.val < 3313 then
[0, 1, 1, 2, 2, 3, 2, 2, 1]
else
[0, 1, 1, 2, 2, 3, 2, 2, 3])
else
(if i.val < 3315 then
[0, 1, 1, 2, 3, 0, 0, 2, 3]
else
[0, 1, 1, 2, 3, 0, 1, 1, 2]))
else
(if i.val < 3318 then
(if i.val < 3317 then
[0, 1, 1, 2, 3, 2, 1, 0, 3]
else
[0, 1, 1, 2, 3, 3, 0, 1, 2])
else
(if i.val < 3319 then
[0, 1, 1, 2, 3, 3, 0, 2, 3]
else
[0, 1, 1, 3, 0, 0, 2, 3, 2])))
else
(if i.val < 3324 then
(if i.val < 3322 then
(if i.val < 3321 then
[0, 1, 1, 3, 0, 0, 2, 3, 3]
else
[0, 1, 1, 3, 0, 1, 1, 0, 2])
else
(if i.val < 3323 then
[0, 1, 1, 3, 0, 1, 1, 2, 1]
else
[0, 1, 1, 3, 0, 1, 1, 2, 2]))
else
(if i.val < 3326 then
(if i.val < 3325 then
[0, 1, 1, 3, 0, 1, 1, 2, 3]
else
[0, 1, 1, 3, 0, 2, 1, 1, 2])
else
(if i.val < 3327 then
[0, 1, 1, 3, 0, 2, 2, 1, 3]
else
[0, 1, 1, 3, 0, 2, 3, 3, 2])))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row18_cosetWordsPart0026 : Fin 4320 → List (Fin 4) :=
  fun i => (if i.val < 3392 then
(if i.val < 3360 then
(if i.val < 3344 then
(if i.val < 3336 then
(if i.val < 3332 then
(if i.val < 3330 then
(if i.val < 3329 then
[0, 1, 1, 3, 2, 1, 0, 0, 3]
else
[0, 1, 1, 3, 2, 1, 0, 3, 2])
else
(if i.val < 3331 then
[0, 1, 1, 3, 2, 2, 1, 1, 3]
else
[0, 1, 1, 3, 3, 0, 1, 2, 1]))
else
(if i.val < 3334 then
(if i.val < 3333 then
[0, 1, 1, 3, 3, 0, 1, 2, 2]
else
[0, 1, 1, 3, 3, 2, 1, 0, 3])
else
(if i.val < 3335 then
[0, 1, 2, 1, 0, 0, 1, 2, 3]
else
[0, 1, 2, 1, 0, 0, 3, 2, 2])))
else
(if i.val < 3340 then
(if i.val < 3338 then
(if i.val < 3337 then
[0, 1, 2, 1, 0, 3, 3, 0, 1]
else
[0, 1, 2, 1, 1, 0, 2, 3, 0])
else
(if i.val < 3339 then
[0, 1, 2, 1, 1, 0, 2, 3, 2]
else
[0, 1, 2, 1, 1, 0, 3, 3, 2]))
else
(if i.val < 3342 then
(if i.val < 3341 then
[0, 1, 2, 1, 1, 2, 3, 0, 0]
else
[0, 1, 2, 1, 1, 2, 3, 3, 0])
else
(if i.val < 3343 then
[0, 1, 2, 1, 1, 3, 0, 1, 2]
else
[0, 1, 2, 1, 1, 3, 2, 2, 1]))))
else
(if i.val < 3352 then
(if i.val < 3348 then
(if i.val < 3346 then
(if i.val < 3345 then
[0, 1, 2, 1, 1, 3, 2, 2, 3]
else
[0, 1, 2, 1, 3, 0, 0, 1, 2])
else
(if i.val < 3347 then
[0, 1, 2, 1, 3, 0, 1, 2, 2]
else
[0, 1, 2, 1, 3, 2, 2, 1, 3]))
else
(if i.val < 3350 then
(if i.val < 3349 then
[0, 1, 2, 1, 3, 2, 2, 3, 0]
else
[0, 1, 2, 1, 3, 3, 0, 1, 2])
else
(if i.val < 3351 then
[0, 1, 2, 1, 3, 3, 0, 2, 2]
else
[0, 1, 2, 1, 3, 3, 2, 2, 1])))
else
(if i.val < 3356 then
(if i.val < 3354 then
(if i.val < 3353 then
[0, 1, 2, 2, 1, 0, 0, 1, 2]
else
[0, 1, 2, 2, 1, 0, 0, 1, 3])
else
(if i.val < 3355 then
[0, 1, 2, 2, 1, 0, 3, 0, 2]
else
[0, 1, 2, 2, 1, 0, 3, 2, 1]))
else
(if i.val < 3358 then
(if i.val < 3357 then
[0, 1, 2, 2, 1, 1, 3, 0, 0]
else
[0, 1, 2, 2, 1, 3, 0, 1, 1])
else
(if i.val < 3359 then
[0, 1, 2, 2, 1, 3, 0, 1, 2]
else
[0, 1, 2, 2, 1, 3, 3, 0, 1])))))
else
(if i.val < 3376 then
(if i.val < 3368 then
(if i.val < 3364 then
(if i.val < 3362 then
(if i.val < 3361 then
[0, 1, 2, 2, 1, 3, 3, 0, 2]
else
[0, 1, 2, 2, 1, 3, 3, 2, 1])
else
(if i.val < 3363 then
[0, 1, 2, 2, 3, 0, 0, 3, 2]
else
[0, 1, 2, 2, 3, 0, 2, 2, 1]))
else
(if i.val < 3366 then
(if i.val < 3365 then
[0, 1, 2, 2, 3, 2, 2, 1, 1]
else
[0, 1, 2, 2, 3, 2, 2, 1, 3])
else
(if i.val < 3367 then
[0, 1, 2, 2, 3, 3, 0, 0, 2]
else
[0, 1, 2, 3, 0, 0, 1, 2, 1])))
else
(if i.val < 3372 then
(if i.val < 3370 then
(if i.val < 3369 then
[0, 1, 2, 3, 0, 0, 1, 2, 3]
else
[0, 1, 2, 3, 0, 0, 3, 2, 2])
else
(if i.val < 3371 then
[0, 1, 2, 3, 0, 1, 1, 2, 1]
else
[0, 1, 2, 3, 0, 1, 1, 2, 3]))
else
(if i.val < 3374 then
(if i.val < 3373 then
[0, 1, 2, 3, 0, 1, 2, 1, 3]
else
[0, 1, 2, 3, 0, 1, 2, 2, 1])
else
(if i.val < 3375 then
[0, 1, 2, 3, 0, 1, 2, 2, 3]
else
[0, 1, 2, 3, 0, 1, 2, 3, 0]))))
else
(if i.val < 3384 then
(if i.val < 3380 then
(if i.val < 3378 then
(if i.val < 3377 then
[0, 1, 2, 3, 0, 1, 2, 3, 3]
else
[0, 1, 2, 3, 0, 2, 1, 1, 2])
else
(if i.val < 3379 then
[0, 1, 2, 3, 0, 2, 2, 1, 1]
else
[0, 1, 2, 3, 2, 1, 0, 3, 2]))
else
(if i.val < 3382 then
(if i.val < 3381 then
[0, 1, 2, 3, 2, 2, 1, 1, 0]
else
[0, 1, 2, 3, 2, 2, 1, 1, 3])
else
(if i.val < 3383 then
[0, 1, 2, 3, 3, 0, 0, 2, 3]
else
[0, 1, 2, 3, 3, 0, 1, 1, 2])))
else
(if i.val < 3388 then
(if i.val < 3386 then
(if i.val < 3385 then
[0, 1, 2, 3, 3, 0, 1, 2, 2]
else
[0, 1, 2, 3, 3, 0, 1, 2, 3])
else
(if i.val < 3387 then
[0, 1, 2, 3, 3, 0, 2, 3, 3]
else
[0, 1, 2, 3, 3, 2, 1, 0, 0]))
else
(if i.val < 3390 then
(if i.val < 3389 then
[0, 1, 2, 3, 3, 2, 1, 0, 3]
else
[0, 1, 2, 3, 3, 2, 2, 1, 1])
else
(if i.val < 3391 then
[0, 1, 3, 0, 0, 1, 1, 2, 1]
else
[0, 1, 3, 0, 0, 1, 1, 2, 2]))))))
else
(if i.val < 3424 then
(if i.val < 3408 then
(if i.val < 3400 then
(if i.val < 3396 then
(if i.val < 3394 then
(if i.val < 3393 then
[0, 1, 3, 0, 0, 1, 1, 2, 3]
else
[0, 1, 3, 0, 0, 1, 2, 1, 1])
else
(if i.val < 3395 then
[0, 1, 3, 0, 0, 1, 2, 1, 3]
else
[0, 1, 3, 0, 0, 1, 2, 2, 3]))
else
(if i.val < 3398 then
(if i.val < 3397 then
[0, 1, 3, 0, 0, 1, 2, 3, 3]
else
[0, 1, 3, 0, 0, 2, 2, 3, 2])
else
(if i.val < 3399 then
[0, 1, 3, 0, 0, 2, 3, 2, 1]
else
[0, 1, 3, 0, 0, 3, 2, 1, 1])))
else
(if i.val < 3404 then
(if i.val < 3402 then
(if i.val < 3401 then
[0, 1, 3, 0, 1, 1, 2, 2, 3]
else
[0, 1, 3, 0, 2, 2, 1, 0, 0])
else
(if i.val < 3403 then
[0, 1, 3, 2, 1, 0, 3, 2, 2]
else
[0, 1, 3, 2, 1, 1, 0, 0, 2]))
else
(if i.val < 3406 then
(if i.val < 3405 then
[0, 1, 3, 2, 1, 1, 0, 2, 3]
else
[0, 1, 3, 2, 1, 1, 2, 3, 3])
else
(if i.val < 3407 then
[0, 1, 3, 2, 2, 1, 0, 3, 2]
else
[0, 1, 3, 2, 2, 3, 0, 1, 1]))))
else
(if i.val < 3416 then
(if i.val < 3412 then
(if i.val < 3410 then
(if i.val < 3409 then
[0, 1, 3, 2, 2, 3, 0, 1, 2]
else
[0, 1, 3, 3, 0, 0, 2, 1, 1])
else
(if i.val < 3411 then
[0, 1, 3, 3, 0, 0, 2, 3, 3]
else
[0, 1, 3, 3, 0, 1, 2, 2, 1]))
else
(if i.val < 3414 then
(if i.val < 3413 then
[0, 1, 3, 3, 0, 1, 2, 3, 0]
else
[0, 1, 3, 3, 0, 2, 1, 0, 0])
else
(if i.val < 3415 then
[0, 1, 3, 3, 0, 2, 1, 1, 2]
else
[0, 1, 3, 3, 0, 2, 3, 3, 0])))
else
(if i.val < 3420 then
(if i.val < 3418 then
(if i.val < 3417 then
[0, 1, 3, 3, 0, 2, 3, 3, 2]
else
[0, 1, 3, 3, 2, 1, 0, 0, 3])
else
(if i.val < 3419 then
[0, 1, 3, 3, 2, 1, 1, 2, 3]
else
[0, 2, 1, 0, 0, 1, 2, 2, 1]))
else
(if i.val < 3422 then
(if i.val < 3421 then
[0, 2, 1, 0, 0, 1, 2, 3, 0]
else
[0, 2, 1, 0, 0, 3, 3, 2, 2])
else
(if i.val < 3423 then
[0, 2, 1, 0, 3, 0, 0, 1, 2]
else
[0, 2, 1, 0, 3, 3, 0, 1, 2])))))
else
(if i.val < 3440 then
(if i.val < 3432 then
(if i.val < 3428 then
(if i.val < 3426 then
(if i.val < 3425 then
[0, 2, 1, 0, 3, 3, 0, 2, 1]
else
[0, 2, 1, 0, 3, 3, 2, 1, 0])
else
(if i.val < 3427 then
[0, 2, 1, 0, 3, 3, 2, 1, 1]
else
[0, 2, 1, 1, 0, 0, 2, 1, 3]))
else
(if i.val < 3430 then
(if i.val < 3429 then
[0, 2, 1, 1, 0, 0, 2, 3, 0]
else
[0, 2, 1, 1, 0, 0, 2, 3, 3])
else
(if i.val < 3431 then
[0, 2, 1, 1, 0, 2, 1, 1, 2]
else
[0, 2, 1, 1, 0, 2, 1, 1, 3])))
else
(if i.val < 3436 then
(if i.val < 3434 then
(if i.val < 3433 then
[0, 2, 1, 1, 0, 2, 3, 0, 0]
else
[0, 2, 1, 1, 0, 2, 3, 0, 1])
else
(if i.val < 3435 then
[0, 2, 1, 1, 0, 2, 3, 2, 1]
else
[0, 2, 1, 1, 0, 3, 0, 2, 1]))
else
(if i.val < 3438 then
(if i.val < 3437 then
[0, 2, 1, 1, 0, 3, 0, 2, 2]
else
[0, 2, 1, 1, 0, 3, 0, 2, 3])
else
(if i.val < 3439 then
[0, 2, 1, 1, 0, 3, 2, 1, 1]
else
[0, 2, 1, 1, 2, 3, 0, 0, 3]))))
else
(if i.val < 3448 then
(if i.val < 3444 then
(if i.val < 3442 then
(if i.val < 3441 then
[0, 2, 1, 1, 2, 3, 2, 1, 0]
else
[0, 2, 1, 1, 2, 3, 3, 0, 1])
else
(if i.val < 3443 then
[0, 2, 1, 1, 2, 3, 3, 2, 1]
else
[0, 2, 1, 1, 3, 2, 2, 1, 0]))
else
(if i.val < 3446 then
(if i.val < 3445 then
[0, 2, 1, 1, 3, 2, 2, 1, 3]
else
[0, 2, 1, 1, 3, 2, 2, 3, 0])
else
(if i.val < 3447 then
[0, 2, 1, 3, 0, 0, 1, 2, 2]
else
[0, 2, 1, 3, 0, 0, 3, 2, 2])))
else
(if i.val < 3452 then
(if i.val < 3450 then
(if i.val < 3449 then
[0, 2, 1, 3, 3, 0, 0, 2, 3]
else
[0, 2, 1, 3, 3, 0, 1, 2, 1])
else
(if i.val < 3451 then
[0, 2, 1, 3, 3, 2, 1, 0, 3]
else
[0, 2, 2, 1, 0, 0, 1, 2, 3]))
else
(if i.val < 3454 then
(if i.val < 3453 then
[0, 2, 2, 1, 0, 0, 1, 3, 2]
else
[0, 2, 2, 1, 0, 3, 2, 1, 1])
else
(if i.val < 3455 then
[0, 2, 2, 1, 1, 0, 3, 2, 1]
else
[0, 2, 2, 1, 1, 3, 2, 2, 3])))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row18_cosetWordsPart0027 : Fin 4320 → List (Fin 4) :=
  fun i => (if i.val < 3520 then
(if i.val < 3488 then
(if i.val < 3472 then
(if i.val < 3464 then
(if i.val < 3460 then
(if i.val < 3458 then
(if i.val < 3457 then
[0, 2, 2, 1, 3, 0, 0, 3, 2]
else
[0, 2, 2, 1, 3, 3, 0, 1, 2])
else
(if i.val < 3459 then
[0, 2, 2, 1, 3, 3, 2, 1, 0]
else
[0, 2, 2, 3, 0, 0, 2, 1, 0]))
else
(if i.val < 3462 then
(if i.val < 3461 then
[0, 2, 2, 3, 0, 0, 2, 1, 1]
else
[0, 2, 2, 3, 0, 1, 2, 3, 3])
else
(if i.val < 3463 then
[0, 2, 2, 3, 0, 2, 1, 1, 2]
else
[0, 2, 2, 3, 0, 2, 2, 1, 3])))
else
(if i.val < 3468 then
(if i.val < 3466 then
(if i.val < 3465 then
[0, 2, 2, 3, 0, 2, 3, 3, 0]
else
[0, 2, 2, 3, 2, 2, 1, 1, 3])
else
(if i.val < 3467 then
[0, 2, 2, 3, 2, 2, 3, 0, 0]
else
[0, 2, 2, 3, 2, 2, 3, 0, 1]))
else
(if i.val < 3470 then
(if i.val < 3469 then
[0, 2, 2, 3, 3, 0, 1, 2, 1]
else
[0, 2, 3, 0, 0, 1, 1, 2, 3])
else
(if i.val < 3471 then
[0, 2, 3, 0, 0, 2, 3, 3, 2]
else
[0, 2, 3, 0, 0, 3, 2, 1, 1]))))
else
(if i.val < 3480 then
(if i.val < 3476 then
(if i.val < 3474 then
(if i.val < 3473 then
[0, 2, 3, 0, 0, 3, 2, 2, 1]
else
[0, 2, 3, 0, 1, 1, 0, 2, 1])
else
(if i.val < 3475 then
[0, 2, 3, 0, 1, 1, 0, 3, 2]
else
[0, 2, 3, 0, 1, 1, 2, 1, 1]))
else
(if i.val < 3478 then
(if i.val < 3477 then
[0, 2, 3, 0, 1, 1, 2, 3, 0]
else
[0, 2, 3, 0, 1, 2, 2, 3, 0])
else
(if i.val < 3479 then
[0, 2, 3, 0, 1, 2, 3, 3, 2]
else
[0, 2, 3, 0, 2, 2, 1, 3, 3])))
else
(if i.val < 3484 then
(if i.val < 3482 then
(if i.val < 3481 then
[0, 2, 3, 0, 2, 2, 3, 3, 0]
else
[0, 2, 3, 0, 2, 3, 3, 0, 2])
else
(if i.val < 3483 then
[0, 2, 3, 0, 2, 3, 3, 2, 1]
else
[0, 2, 3, 2, 1, 0, 3, 2, 1]))
else
(if i.val < 3486 then
(if i.val < 3485 then
[0, 2, 3, 2, 1, 0, 3, 2, 2]
else
[0, 2, 3, 2, 1, 1, 0, 3, 2])
else
(if i.val < 3487 then
[0, 2, 3, 2, 2, 1, 1, 0, 0]
else
[0, 2, 3, 2, 2, 1, 3, 0, 0])))))
else
(if i.val < 3504 then
(if i.val < 3496 then
(if i.val < 3492 then
(if i.val < 3490 then
(if i.val < 3489 then
[0, 2, 3, 2, 2, 1, 3, 0, 1]
else
[0, 2, 3, 2, 2, 3, 0, 1, 2])
else
(if i.val < 3491 then
[0, 2, 3, 3, 0, 0, 2, 1, 3]
else
[0, 2, 3, 3, 0, 1, 1, 0, 2]))
else
(if i.val < 3494 then
(if i.val < 3493 then
[0, 2, 3, 3, 0, 1, 2, 1, 1]
else
[0, 2, 3, 3, 0, 1, 2, 1, 3])
else
(if i.val < 3495 then
[0, 2, 3, 3, 0, 2, 1, 0, 0]
else
[0, 2, 3, 3, 0, 2, 3, 3, 2])))
else
(if i.val < 3500 then
(if i.val < 3498 then
(if i.val < 3497 then
[0, 2, 3, 3, 2, 1, 0, 0, 3]
else
[0, 3, 0, 0, 1, 1, 2, 1, 1])
else
(if i.val < 3499 then
[0, 3, 0, 0, 1, 1, 2, 1, 3]
else
[0, 3, 0, 0, 1, 1, 2, 2, 1]))
else
(if i.val < 3502 then
(if i.val < 3501 then
[0, 3, 0, 0, 1, 1, 2, 3, 0]
else
[0, 3, 0, 0, 1, 2, 3, 0, 2])
else
(if i.val < 3503 then
[0, 3, 0, 0, 1, 2, 3, 3, 2]
else
[0, 3, 0, 0, 2, 1, 1, 0, 2]))))
else
(if i.val < 3512 then
(if i.val < 3508 then
(if i.val < 3506 then
(if i.val < 3505 then
[0, 3, 0, 0, 2, 1, 1, 2, 3]
else
[0, 3, 0, 0, 2, 2, 1, 0, 0])
else
(if i.val < 3507 then
[0, 3, 0, 0, 2, 2, 3, 2, 2]
else
[0, 3, 0, 0, 2, 3, 3, 2, 1]))
else
(if i.val < 3510 then
(if i.val < 3509 then
[0, 3, 0, 0, 3, 2, 1, 0, 0]
else
[0, 3, 0, 0, 3, 2, 1, 1, 0])
else
(if i.val < 3511 then
[0, 3, 0, 0, 3, 2, 1, 1, 2]
else
[0, 3, 0, 0, 3, 2, 2, 1, 0])))
else
(if i.val < 3516 then
(if i.val < 3514 then
(if i.val < 3513 then
[0, 3, 0, 0, 3, 2, 2, 1, 3]
else
[0, 3, 0, 1, 1, 0, 2, 3, 3])
else
(if i.val < 3515 then
[0, 3, 0, 1, 1, 0, 3, 2, 1]
else
[0, 3, 0, 1, 1, 2, 1, 0, 3]))
else
(if i.val < 3518 then
(if i.val < 3517 then
[0, 3, 0, 1, 1, 2, 1, 1, 0]
else
[0, 3, 0, 1, 1, 2, 1, 1, 2])
else
(if i.val < 3519 then
[0, 3, 0, 1, 1, 2, 2, 1, 1]
else
[0, 3, 0, 1, 1, 2, 3, 3, 0]))))))
else
(if i.val < 3552 then
(if i.val < 3536 then
(if i.val < 3528 then
(if i.val < 3524 then
(if i.val < 3522 then
(if i.val < 3521 then
[0, 3, 0, 1, 2, 1, 1, 2, 3]
else
[0, 3, 0, 1, 2, 2, 3, 0, 0])
else
(if i.val < 3523 then
[0, 3, 0, 1, 2, 3, 0, 1, 1]
else
[0, 3, 0, 1, 2, 3, 0, 1, 2]))
else
(if i.val < 3526 then
(if i.val < 3525 then
[0, 3, 0, 1, 2, 3, 3, 0, 1]
else
[0, 3, 0, 1, 2, 3, 3, 0, 2])
else
(if i.val < 3527 then
[0, 3, 0, 2, 1, 1, 0, 2, 1]
else
[0, 3, 0, 2, 1, 1, 0, 3, 2])))
else
(if i.val < 3532 then
(if i.val < 3530 then
(if i.val < 3529 then
[0, 3, 0, 2, 1, 1, 2, 3, 0]
else
[0, 3, 0, 2, 1, 1, 3, 2, 2])
else
(if i.val < 3531 then
[0, 3, 0, 2, 1, 3, 3, 0, 1]
else
[0, 3, 0, 2, 1, 3, 3, 2, 2]))
else
(if i.val < 3534 then
(if i.val < 3533 then
[0, 3, 0, 2, 2, 1, 0, 3, 3]
else
[0, 3, 0, 2, 2, 1, 1, 3, 0])
else
(if i.val < 3535 then
[0, 3, 0, 2, 2, 1, 3, 3, 2]
else
[0, 3, 0, 2, 3, 3, 0, 2, 1]))))
else
(if i.val < 3544 then
(if i.val < 3540 then
(if i.val < 3538 then
(if i.val < 3537 then
[0, 3, 0, 2, 3, 3, 2, 1, 0]
else
[0, 3, 2, 1, 0, 0, 1, 2, 2])
else
(if i.val < 3539 then
[0, 3, 2, 1, 0, 0, 3, 2, 1]
else
[0, 3, 2, 1, 0, 3, 2, 1, 0]))
else
(if i.val < 3542 then
(if i.val < 3541 then
[0, 3, 2, 1, 0, 3, 2, 1, 1]
else
[0, 3, 2, 1, 0, 3, 2, 2, 3])
else
(if i.val < 3543 then
[0, 3, 2, 1, 1, 0, 0, 2, 3]
else
[0, 3, 2, 1, 1, 0, 0, 3, 2])))
else
(if i.val < 3548 then
(if i.val < 3546 then
(if i.val < 3545 then
[0, 3, 2, 1, 1, 0, 2, 3, 2]
else
[0, 3, 2, 1, 1, 0, 2, 3, 3])
else
(if i.val < 3547 then
[0, 3, 2, 1, 1, 0, 3, 2, 1]
else
[0, 3, 2, 1, 1, 2, 3, 0, 1]))
else
(if i.val < 3550 then
(if i.val < 3549 then
[0, 3, 2, 2, 1, 0, 0, 1, 3]
else
[0, 3, 2, 2, 1, 1, 3, 0, 0])
else
(if i.val < 3551 then
[0, 3, 2, 2, 1, 3, 0, 1, 1]
else
[0, 3, 2, 2, 1, 3, 0, 1, 2])))))
else
(if i.val < 3568 then
(if i.val < 3560 then
(if i.val < 3556 then
(if i.val < 3554 then
(if i.val < 3553 then
[0, 3, 2, 2, 1, 3, 2, 2, 3]
else
[0, 3, 2, 2, 3, 0, 0, 3, 2])
else
(if i.val < 3555 then
[0, 3, 3, 0, 0, 2, 1, 0, 0]
else
[0, 3, 3, 0, 1, 1, 0, 2, 3]))
else
(if i.val < 3558 then
(if i.val < 3557 then
[0, 3, 3, 0, 1, 1, 0, 3, 2]
else
[0, 3, 3, 0, 1, 2, 1, 1, 0])
else
(if i.val < 3559 then
[0, 3, 3, 0, 1, 2, 1, 1, 3]
else
[0, 3, 3, 0, 1, 2, 2, 3, 3])))
else
(if i.val < 3564 then
(if i.val < 3562 then
(if i.val < 3561 then
[0, 3, 3, 0, 1, 2, 3, 0, 1]
else
[0, 3, 3, 0, 1, 2, 3, 3, 2])
else
(if i.val < 3563 then
[0, 3, 3, 0, 2, 1, 0, 3, 3]
else
[0, 3, 3, 0, 2, 1, 1, 2, 3]))
else
(if i.val < 3566 then
(if i.val < 3565 then
[0, 3, 3, 0, 2, 3, 3, 0, 2]
else
[0, 3, 3, 0, 2, 3, 3, 2, 1])
else
(if i.val < 3567 then
[0, 3, 3, 2, 1, 0, 3, 2, 2]
else
[0, 3, 3, 2, 1, 1, 0, 3, 3]))))
else
(if i.val < 3576 then
(if i.val < 3572 then
(if i.val < 3570 then
(if i.val < 3569 then
[0, 3, 3, 2, 1, 1, 2, 3, 3]
else
[1, 0, 0, 1, 2, 1, 0, 0, 3])
else
(if i.val < 3571 then
[1, 0, 0, 1, 2, 1, 0, 3, 0]
else
[1, 0, 0, 1, 2, 1, 0, 3, 3]))
else
(if i.val < 3574 then
(if i.val < 3573 then
[1, 0, 0, 1, 2, 1, 1, 0, 3]
else
[1, 0, 0, 1, 2, 1, 1, 2, 3])
else
(if i.val < 3575 then
[1, 0, 0, 1, 2, 1, 3, 0, 0]
else
[1, 0, 0, 1, 2, 1, 3, 0, 1])))
else
(if i.val < 3580 then
(if i.val < 3578 then
(if i.val < 3577 then
[1, 0, 0, 1, 2, 1, 3, 3, 0]
else
[1, 0, 0, 1, 2, 2, 1, 0, 0])
else
(if i.val < 3579 then
[1, 0, 0, 1, 2, 2, 3, 2, 1]
else
[1, 0, 0, 1, 2, 3, 0, 0, 3]))
else
(if i.val < 3582 then
(if i.val < 3581 then
[1, 0, 0, 1, 2, 3, 3, 0, 0]
else
[1, 0, 0, 1, 2, 3, 3, 2, 2])
else
(if i.val < 3583 then
[1, 0, 0, 1, 3, 2, 1, 1, 2]
else
[1, 0, 0, 1, 3, 3, 0, 1, 2])))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row18_cosetWordsPart0028 : Fin 4320 → List (Fin 4) :=
  fun i => (if i.val < 3648 then
(if i.val < 3616 then
(if i.val < 3600 then
(if i.val < 3592 then
(if i.val < 3588 then
(if i.val < 3586 then
(if i.val < 3585 then
[1, 0, 0, 1, 3, 3, 0, 2, 2]
else
[1, 0, 0, 1, 3, 3, 0, 2, 3])
else
(if i.val < 3587 then
[1, 0, 0, 2, 1, 1, 0, 2, 1]
else
[1, 0, 0, 2, 1, 1, 2, 3, 0]))
else
(if i.val < 3590 then
(if i.val < 3589 then
[1, 0, 0, 2, 1, 1, 3, 0, 2]
else
[1, 0, 0, 2, 1, 3, 3, 2, 2])
else
(if i.val < 3591 then
[1, 0, 0, 2, 2, 1, 0, 3, 2]
else
[1, 0, 0, 2, 2, 3, 2, 2, 3])))
else
(if i.val < 3596 then
(if i.val < 3594 then
(if i.val < 3593 then
[1, 0, 0, 2, 3, 0, 0, 2, 2]
else
[1, 0, 0, 2, 3, 0, 2, 2, 1])
else
(if i.val < 3595 then
[1, 0, 0, 2, 3, 2, 1, 0, 3]
else
[1, 0, 0, 2, 3, 2, 1, 1, 0]))
else
(if i.val < 3598 then
(if i.val < 3597 then
[1, 0, 0, 2, 3, 2, 2, 1, 3]
else
[1, 0, 0, 2, 3, 3, 0, 1, 2])
else
(if i.val < 3599 then
[1, 0, 0, 2, 3, 3, 0, 2, 2]
else
[1, 0, 0, 3, 0, 0, 1, 1, 2]))))
else
(if i.val < 3608 then
(if i.val < 3604 then
(if i.val < 3602 then
(if i.val < 3601 then
[1, 0, 0, 3, 0, 0, 3, 2, 1]
else
[1, 0, 0, 3, 0, 1, 2, 3, 3])
else
(if i.val < 3603 then
[1, 0, 0, 3, 0, 2, 1, 1, 2]
else
[1, 0, 0, 3, 2, 1, 1, 2, 3]))
else
(if i.val < 3606 then
(if i.val < 3605 then
[1, 0, 0, 3, 2, 2, 3, 0, 0]
else
[1, 0, 0, 3, 3, 0, 0, 2, 3])
else
(if i.val < 3607 then
[1, 0, 0, 3, 3, 0, 2, 1, 3]
else
[1, 0, 0, 3, 3, 2, 1, 0, 0])))
else
(if i.val < 3612 then
(if i.val < 3610 then
(if i.val < 3609 then
[1, 0, 0, 3, 3, 2, 1, 0, 3]
else
[1, 0, 0, 3, 3, 2, 2, 1, 0])
else
(if i.val < 3611 then
[1, 0, 2, 1, 0, 3, 3, 0, 1]
else
[1, 0, 2, 1, 0, 3, 3, 2, 1]))
else
(if i.val < 3614 then
(if i.val < 3613 then
[1, 0, 2, 1, 1, 0, 0, 2, 1]
else
[1, 0, 2, 1, 1, 0, 0, 2, 3])
else
(if i.val < 3615 then
[1, 0, 2, 1, 1, 0, 2, 1, 1]
else
[1, 0, 2, 1, 1, 0, 2, 1, 3])))))
else
(if i.val < 3632 then
(if i.val < 3624 then
(if i.val < 3620 then
(if i.val < 3618 then
(if i.val < 3617 then
[1, 0, 2, 1, 1, 0, 2, 3, 0]
else
[1, 0, 2, 1, 1, 0, 3, 2, 1])
else
(if i.val < 3619 then
[1, 0, 2, 1, 1, 2, 3, 3, 0]
else
[1, 0, 2, 1, 1, 3, 0, 2, 2]))
else
(if i.val < 3622 then
(if i.val < 3621 then
[1, 0, 2, 1, 1, 3, 2, 2, 3]
else
[1, 0, 2, 1, 3, 3, 0, 1, 2])
else
(if i.val < 3623 then
[1, 0, 2, 1, 3, 3, 2, 2, 1]
else
[1, 0, 2, 2, 1, 3, 3, 0, 2])))
else
(if i.val < 3628 then
(if i.val < 3626 then
(if i.val < 3625 then
[1, 0, 2, 2, 3, 0, 0, 2, 2]
else
[1, 0, 2, 2, 3, 0, 2, 2, 1])
else
(if i.val < 3627 then
[1, 0, 2, 2, 3, 2, 2, 1, 0]
else
[1, 0, 2, 2, 3, 2, 2, 1, 3]))
else
(if i.val < 3630 then
(if i.val < 3629 then
[1, 0, 2, 2, 3, 3, 0, 0, 2]
else
[1, 0, 2, 3, 0, 0, 2, 1, 0])
else
(if i.val < 3631 then
[1, 0, 2, 3, 0, 1, 1, 0, 2]
else
[1, 0, 2, 3, 0, 1, 1, 2, 1]))))
else
(if i.val < 3640 then
(if i.val < 3636 then
(if i.val < 3634 then
(if i.val < 3633 then
[1, 0, 2, 3, 0, 1, 1, 2, 3]
else
[1, 0, 2, 3, 0, 1, 2, 2, 3])
else
(if i.val < 3635 then
[1, 0, 2, 3, 0, 2, 1, 0, 3]
else
[1, 0, 2, 3, 0, 2, 1, 3, 3]))
else
(if i.val < 3638 then
(if i.val < 3637 then
[1, 0, 2, 3, 0, 2, 3, 3, 2]
else
[1, 0, 2, 3, 2, 1, 0, 3, 2])
else
(if i.val < 3639 then
[1, 0, 2, 3, 2, 1, 1, 0, 0]
else
[1, 0, 2, 3, 3, 0, 0, 2, 3])))
else
(if i.val < 3644 then
(if i.val < 3642 then
(if i.val < 3641 then
[1, 0, 2, 3, 3, 0, 1, 2, 1]
else
[1, 0, 2, 3, 3, 0, 2, 1, 1])
else
(if i.val < 3643 then
[1, 0, 2, 3, 3, 0, 2, 1, 3]
else
[1, 0, 2, 3, 3, 0, 2, 3, 3]))
else
(if i.val < 3646 then
(if i.val < 3645 then
[1, 0, 2, 3, 3, 2, 1, 0, 0]
else
[1, 0, 2, 3, 3, 2, 1, 0, 3])
else
(if i.val < 3647 then
[1, 0, 3, 0, 0, 1, 1, 2, 1]
else
[1, 0, 3, 0, 0, 1, 1, 2, 3]))))))
else
(if i.val < 3680 then
(if i.val < 3664 then
(if i.val < 3656 then
(if i.val < 3652 then
(if i.val < 3650 then
(if i.val < 3649 then
[1, 0, 3, 0, 0, 1, 2, 1, 1]
else
[1, 0, 3, 0, 0, 1, 2, 3, 3])
else
(if i.val < 3651 then
[1, 0, 3, 0, 0, 2, 1, 0, 0]
else
[1, 0, 3, 0, 0, 2, 3, 3, 2]))
else
(if i.val < 3654 then
(if i.val < 3653 then
[1, 0, 3, 0, 0, 3, 2, 1, 0]
else
[1, 0, 3, 0, 0, 3, 2, 2, 1])
else
(if i.val < 3655 then
[1, 0, 3, 0, 1, 1, 2, 1, 1]
else
[1, 0, 3, 0, 1, 2, 3, 0, 1])))
else
(if i.val < 3660 then
(if i.val < 3658 then
(if i.val < 3657 then
[1, 0, 3, 0, 1, 2, 3, 3, 2]
else
[1, 0, 3, 0, 2, 1, 0, 3, 3])
else
(if i.val < 3659 then
[1, 0, 3, 0, 2, 1, 1, 0, 2]
else
[1, 0, 3, 0, 2, 1, 1, 0, 3]))
else
(if i.val < 3662 then
(if i.val < 3661 then
[1, 0, 3, 0, 2, 3, 3, 0, 1]
else
[1, 0, 3, 0, 2, 3, 3, 2, 1])
else
(if i.val < 3663 then
[1, 0, 3, 2, 1, 1, 0, 2, 1]
else
[1, 0, 3, 2, 1, 1, 0, 3, 2]))))
else
(if i.val < 3672 then
(if i.val < 3668 then
(if i.val < 3666 then
(if i.val < 3665 then
[1, 0, 3, 2, 1, 1, 2, 3, 0]
else
[1, 0, 3, 2, 2, 1, 0, 0, 3])
else
(if i.val < 3667 then
[1, 0, 3, 2, 2, 1, 0, 3, 2]
else
[1, 0, 3, 2, 2, 1, 3, 0, 0]))
else
(if i.val < 3670 then
(if i.val < 3669 then
[1, 0, 3, 2, 2, 3, 0, 0, 3]
else
[1, 0, 3, 2, 2, 3, 0, 1, 2])
else
(if i.val < 3671 then
[1, 0, 3, 3, 0, 1, 2, 1, 0]
else
[1, 0, 3, 3, 0, 1, 2, 1, 1])))
else
(if i.val < 3676 then
(if i.val < 3674 then
(if i.val < 3673 then
[1, 0, 3, 3, 0, 1, 2, 1, 3]
else
[1, 0, 3, 3, 0, 1, 2, 2, 1])
else
(if i.val < 3675 then
[1, 0, 3, 3, 0, 1, 2, 2, 3]
else
[1, 0, 3, 3, 0, 2, 3, 3, 2]))
else
(if i.val < 3678 then
(if i.val < 3677 then
[1, 1, 0, 0, 2, 1, 1, 2, 3]
else
[1, 1, 0, 0, 3, 0, 1, 2, 1])
else
(if i.val < 3679 then
[1, 1, 0, 2, 1, 0, 0, 1, 2]
else
[1, 1, 0, 2, 1, 0, 3, 3, 2])))))
else
(if i.val < 3696 then
(if i.val < 3688 then
(if i.val < 3684 then
(if i.val < 3682 then
(if i.val < 3681 then
[1, 1, 0, 2, 1, 1, 0, 2, 1]
else
[1, 1, 0, 2, 1, 1, 0, 2, 3])
else
(if i.val < 3683 then
[1, 1, 0, 2, 1, 1, 0, 3, 2]
else
[1, 1, 0, 2, 1, 1, 2, 3, 3]))
else
(if i.val < 3686 then
(if i.val < 3685 then
[1, 1, 0, 2, 1, 1, 3, 0, 2]
else
[1, 1, 0, 2, 1, 1, 3, 2, 2])
else
(if i.val < 3687 then
[1, 1, 0, 2, 1, 3, 3, 0, 1]
else
[1, 1, 0, 2, 1, 3, 3, 2, 2])))
else
(if i.val < 3692 then
(if i.val < 3690 then
(if i.val < 3689 then
[1, 1, 0, 2, 2, 1, 0, 3, 3]
else
[1, 1, 0, 2, 2, 1, 3, 3, 2])
else
(if i.val < 3691 then
[1, 1, 0, 2, 2, 3, 0, 2, 3]
else
[1, 1, 0, 2, 2, 3, 2, 1, 1]))
else
(if i.val < 3694 then
(if i.val < 3693 then
[1, 1, 0, 2, 2, 3, 2, 2, 3]
else
[1, 1, 0, 2, 3, 0, 0, 2, 3])
else
(if i.val < 3695 then
[1, 1, 0, 2, 3, 0, 1, 1, 2]
else
[1, 1, 0, 2, 3, 0, 2, 1, 0]))))
else
(if i.val < 3704 then
(if i.val < 3700 then
(if i.val < 3698 then
(if i.val < 3697 then
[1, 1, 0, 2, 3, 0, 2, 1, 1]
else
[1, 1, 0, 2, 3, 2, 1, 0, 0])
else
(if i.val < 3699 then
[1, 1, 0, 2, 3, 2, 1, 0, 3]
else
[1, 1, 0, 2, 3, 3, 0, 1, 2]))
else
(if i.val < 3702 then
(if i.val < 3701 then
[1, 1, 0, 2, 3, 3, 0, 2, 1]
else
[1, 1, 0, 3, 0, 0, 1, 1, 2])
else
(if i.val < 3703 then
[1, 1, 0, 3, 0, 0, 1, 3, 2]
else
[1, 1, 0, 3, 0, 0, 2, 1, 1])))
else
(if i.val < 3708 then
(if i.val < 3706 then
(if i.val < 3705 then
[1, 1, 0, 3, 0, 0, 2, 2, 1]
else
[1, 1, 0, 3, 0, 0, 2, 3, 2])
else
(if i.val < 3707 then
[1, 1, 0, 3, 0, 0, 3, 2, 1]
else
[1, 1, 0, 3, 0, 1, 2, 3, 3]))
else
(if i.val < 3710 then
(if i.val < 3709 then
[1, 1, 0, 3, 0, 2, 1, 0, 0]
else
[1, 1, 0, 3, 0, 2, 1, 0, 3])
else
(if i.val < 3711 then
[1, 1, 0, 3, 0, 2, 1, 1, 0]
else
[1, 1, 0, 3, 0, 2, 2, 1, 3])))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row18_cosetWordsPart0029 : Fin 4320 → List (Fin 4) :=
  fun i => (if i.val < 3776 then
(if i.val < 3744 then
(if i.val < 3728 then
(if i.val < 3720 then
(if i.val < 3716 then
(if i.val < 3714 then
(if i.val < 3713 then
[1, 1, 0, 3, 0, 2, 3, 3, 2]
else
[1, 1, 0, 3, 2, 1, 0, 0, 3])
else
(if i.val < 3715 then
[1, 1, 0, 3, 2, 1, 1, 0, 0]
else
[1, 1, 0, 3, 2, 1, 1, 2, 3]))
else
(if i.val < 3718 then
(if i.val < 3717 then
[1, 1, 0, 3, 2, 2, 1, 1, 3]
else
[1, 1, 0, 3, 2, 2, 3, 0, 0])
else
(if i.val < 3719 then
[1, 1, 0, 3, 2, 2, 3, 0, 1]
else
[1, 1, 0, 3, 3, 0, 1, 2, 2])))
else
(if i.val < 3724 then
(if i.val < 3722 then
(if i.val < 3721 then
[1, 1, 2, 1, 0, 3, 0, 2, 2]
else
[1, 1, 2, 1, 0, 3, 3, 0, 1])
else
(if i.val < 3723 then
[1, 1, 2, 1, 1, 0, 2, 3, 2]
else
[1, 1, 2, 1, 1, 0, 3, 0, 2]))
else
(if i.val < 3726 then
(if i.val < 3725 then
[1, 1, 2, 1, 1, 2, 3, 0, 1]
else
[1, 1, 2, 1, 3, 3, 0, 2, 2])
else
(if i.val < 3727 then
[1, 1, 2, 1, 3, 3, 2, 2, 1]
else
[1, 1, 2, 2, 1, 0, 3, 2, 1]))))
else
(if i.val < 3736 then
(if i.val < 3732 then
(if i.val < 3730 then
(if i.val < 3729 then
[1, 1, 2, 2, 1, 1, 3, 0, 2]
else
[1, 1, 2, 2, 1, 3, 0, 1, 2])
else
(if i.val < 3731 then
[1, 1, 2, 2, 1, 3, 3, 2, 1]
else
[1, 1, 2, 2, 3, 2, 2, 1, 3]))
else
(if i.val < 3734 then
(if i.val < 3733 then
[1, 1, 2, 3, 0, 0, 1, 1, 2]
else
[1, 1, 2, 3, 0, 1, 1, 2, 1])
else
(if i.val < 3735 then
[1, 1, 2, 3, 0, 1, 2, 2, 1]
else
[1, 1, 2, 3, 0, 1, 2, 2, 3])))
else
(if i.val < 3740 then
(if i.val < 3738 then
(if i.val < 3737 then
[1, 1, 2, 3, 0, 1, 2, 3, 0]
else
[1, 1, 2, 3, 3, 0, 1, 1, 2])
else
(if i.val < 3739 then
[1, 1, 2, 3, 3, 2, 1, 0, 3]
else
[1, 1, 3, 0, 0, 1, 1, 2, 3]))
else
(if i.val < 3742 then
(if i.val < 3741 then
[1, 1, 3, 0, 0, 2, 3, 2, 1]
else
[1, 1, 3, 0, 1, 1, 0, 2, 1])
else
(if i.val < 3743 then
[1, 1, 3, 0, 1, 1, 2, 1, 0]
else
[1, 1, 3, 0, 1, 1, 2, 2, 1])))))
else
(if i.val < 3760 then
(if i.val < 3752 then
(if i.val < 3748 then
(if i.val < 3746 then
(if i.val < 3745 then
[1, 1, 3, 0, 1, 1, 2, 2, 3]
else
[1, 1, 3, 0, 1, 2, 3, 0, 1])
else
(if i.val < 3747 then
[1, 1, 3, 0, 1, 2, 3, 3, 2]
else
[1, 1, 3, 0, 2, 3, 3, 2, 1]))
else
(if i.val < 3750 then
(if i.val < 3749 then
[1, 1, 3, 2, 1, 0, 3, 2, 2]
else
[1, 1, 3, 2, 2, 1, 0, 3, 2])
else
(if i.val < 3751 then
[1, 1, 3, 2, 2, 3, 0, 1, 2]
else
[1, 1, 3, 3, 0, 1, 2, 2, 1])))
else
(if i.val < 3756 then
(if i.val < 3754 then
(if i.val < 3753 then
[1, 1, 3, 3, 0, 2, 3, 3, 2]
else
[1, 2, 1, 0, 0, 3, 2, 2, 1])
else
(if i.val < 3755 then
[1, 2, 1, 0, 0, 3, 3, 2, 2]
else
[1, 2, 1, 0, 3, 0, 1, 1, 2]))
else
(if i.val < 3758 then
(if i.val < 3757 then
[1, 2, 1, 0, 3, 0, 1, 2, 3]
else
[1, 2, 1, 0, 3, 0, 2, 2, 1])
else
(if i.val < 3759 then
[1, 2, 1, 1, 0, 0, 2, 1, 3]
else
[1, 2, 1, 1, 0, 2, 3, 0, 0]))))
else
(if i.val < 3768 then
(if i.val < 3764 then
(if i.val < 3762 then
(if i.val < 3761 then
[1, 2, 1, 1, 0, 2, 3, 0, 1]
else
[1, 2, 1, 1, 0, 2, 3, 0, 2])
else
(if i.val < 3763 then
[1, 2, 1, 1, 0, 2, 3, 2, 1]
else
[1, 2, 1, 1, 2, 3, 3, 0, 1]))
else
(if i.val < 3766 then
(if i.val < 3765 then
[1, 2, 1, 1, 3, 2, 2, 1, 3]
else
[1, 2, 1, 1, 3, 2, 2, 3, 0])
else
(if i.val < 3767 then
[1, 2, 1, 3, 0, 0, 3, 2, 2]
else
[1, 2, 1, 3, 0, 1, 2, 2, 1])))
else
(if i.val < 3772 then
(if i.val < 3770 then
(if i.val < 3769 then
[1, 2, 1, 3, 0, 1, 2, 3, 0]
else
[1, 2, 1, 3, 0, 1, 2, 3, 3])
else
(if i.val < 3771 then
[1, 2, 1, 3, 3, 0, 1, 2, 2]
else
[1, 2, 1, 3, 3, 2, 2, 1, 1]))
else
(if i.val < 3774 then
(if i.val < 3773 then
[1, 2, 2, 1, 0, 0, 1, 2, 3]
else
[1, 2, 2, 1, 0, 3, 0, 2, 1])
else
(if i.val < 3775 then
[1, 2, 2, 1, 0, 3, 2, 1, 0]
else
[1, 2, 2, 1, 0, 3, 2, 1, 1]))))))
else
(if i.val < 3808 then
(if i.val < 3792 then
(if i.val < 3784 then
(if i.val < 3780 then
(if i.val < 3778 then
(if i.val < 3777 then
[1, 2, 2, 1, 1, 3, 2, 1, 0]
else
[1, 2, 2, 3, 0, 0, 1, 2, 2])
else
(if i.val < 3779 then
[1, 2, 2, 3, 0, 1, 2, 3, 3]
else
[1, 2, 2, 3, 0, 2, 2, 1, 3]))
else
(if i.val < 3782 then
(if i.val < 3781 then
[1, 2, 2, 3, 2, 2, 1, 1, 3]
else
[1, 2, 3, 0, 0, 3, 2, 2, 1])
else
(if i.val < 3783 then
[1, 2, 3, 0, 1, 1, 2, 1, 0]
else
[1, 2, 3, 0, 1, 1, 2, 1, 1])))
else
(if i.val < 3788 then
(if i.val < 3786 then
(if i.val < 3785 then
[1, 2, 3, 0, 1, 2, 1, 3, 0]
else
[1, 2, 3, 0, 1, 2, 1, 3, 3])
else
(if i.val < 3787 then
[1, 2, 3, 0, 1, 2, 2, 1, 3]
else
[1, 2, 3, 0, 1, 2, 2, 3, 0]))
else
(if i.val < 3790 then
(if i.val < 3789 then
[1, 2, 3, 0, 1, 2, 3, 3, 2]
else
[1, 2, 3, 0, 2, 3, 3, 2, 1])
else
(if i.val < 3791 then
[1, 2, 3, 2, 1, 0, 3, 2, 2]
else
[1, 2, 3, 2, 2, 1, 3, 2, 2]))))
else
(if i.val < 3800 then
(if i.val < 3796 then
(if i.val < 3794 then
(if i.val < 3793 then
[1, 2, 3, 3, 0, 1, 2, 1, 0]
else
[1, 2, 3, 3, 0, 1, 2, 1, 3])
else
(if i.val < 3795 then
[1, 2, 3, 3, 0, 1, 2, 3, 3]
else
[1, 2, 3, 3, 0, 2, 1, 3, 3]))
else
(if i.val < 3798 then
(if i.val < 3797 then
[1, 2, 3, 3, 2, 1, 0, 0, 3]
else
[1, 3, 0, 0, 1, 1, 2, 1, 1])
else
(if i.val < 3799 then
[1, 3, 0, 0, 1, 1, 2, 1, 3]
else
[1, 3, 0, 0, 1, 2, 1, 1, 3])))
else
(if i.val < 3804 then
(if i.val < 3802 then
(if i.val < 3801 then
[1, 3, 0, 0, 1, 2, 1, 3, 3]
else
[1, 3, 0, 0, 1, 2, 2, 1, 3])
else
(if i.val < 3803 then
[1, 3, 0, 0, 1, 2, 3, 0, 1]
else
[1, 3, 0, 0, 1, 2, 3, 0, 2]))
else
(if i.val < 3806 then
(if i.val < 3805 then
[1, 3, 0, 0, 1, 2, 3, 3, 2]
else
[1, 3, 0, 0, 2, 1, 1, 0, 2])
else
(if i.val < 3807 then
[1, 3, 0, 0, 2, 1, 1, 2, 3]
else
[1, 3, 0, 0, 2, 2, 3, 2, 2])))))
else
(if i.val < 3824 then
(if i.val < 3816 then
(if i.val < 3812 then
(if i.val < 3810 then
(if i.val < 3809 then
[1, 3, 0, 0, 2, 3, 2, 1, 1]
else
[1, 3, 0, 0, 3, 2, 1, 1, 0])
else
(if i.val < 3811 then
[1, 3, 0, 0, 3, 2, 1, 1, 2]
else
[1, 3, 0, 0, 3, 2, 2, 1, 3]))
else
(if i.val < 3814 then
(if i.val < 3813 then
[1, 3, 0, 1, 1, 0, 2, 3, 3]
else
[1, 3, 0, 1, 1, 2, 3, 3, 0])
else
(if i.val < 3815 then
[1, 3, 0, 1, 2, 1, 1, 0, 2]
else
[1, 3, 0, 1, 2, 1, 1, 0, 3])))
else
(if i.val < 3820 then
(if i.val < 3818 then
(if i.val < 3817 then
[1, 3, 0, 1, 2, 3, 3, 0, 1]
else
[1, 3, 0, 2, 1, 1, 0, 2, 1])
else
(if i.val < 3819 then
[1, 3, 0, 2, 1, 1, 2, 3, 3]
else
[1, 3, 0, 2, 2, 1, 3, 3, 2]))
else
(if i.val < 3822 then
(if i.val < 3821 then
[1, 3, 0, 2, 3, 3, 0, 2, 1]
else
[1, 3, 2, 1, 1, 0, 0, 2, 3])
else
(if i.val < 3823 then
[1, 3, 2, 1, 1, 0, 0, 3, 2]
else
[1, 3, 2, 2, 1, 0, 0, 3, 2]))))
else
(if i.val < 3832 then
(if i.val < 3828 then
(if i.val < 3826 then
(if i.val < 3825 then
[1, 3, 2, 2, 1, 0, 3, 2, 1]
else
[1, 3, 2, 2, 1, 3, 0, 1, 2])
else
(if i.val < 3827 then
[1, 3, 2, 2, 3, 0, 0, 1, 2]
else
[1, 3, 3, 0, 0, 1, 2, 3, 0]))
else
(if i.val < 3830 then
(if i.val < 3829 then
[1, 3, 3, 0, 0, 2, 3, 3, 2]
else
[1, 3, 3, 0, 1, 2, 1, 1, 0])
else
(if i.val < 3831 then
[1, 3, 3, 0, 1, 2, 2, 1, 0]
else
[1, 3, 3, 0, 1, 2, 3, 0, 0])))
else
(if i.val < 3836 then
(if i.val < 3834 then
(if i.val < 3833 then
[1, 3, 3, 0, 1, 2, 3, 0, 1]
else
[1, 3, 3, 0, 2, 1, 1, 2, 3])
else
(if i.val < 3835 then
[2, 1, 0, 0, 1, 2, 2, 1, 0]
else
[2, 1, 0, 0, 1, 2, 2, 1, 3]))
else
(if i.val < 3838 then
(if i.val < 3837 then
[2, 1, 0, 0, 1, 2, 3, 0, 0]
else
[2, 1, 0, 0, 1, 3, 2, 2, 1])
else
(if i.val < 3839 then
[2, 1, 0, 0, 3, 0, 1, 2, 3]
else
[2, 1, 0, 3, 0, 0, 2, 1, 0])))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row18_cosetWordsPart0030 : Fin 4320 → List (Fin 4) :=
  fun i => (if i.val < 3904 then
(if i.val < 3872 then
(if i.val < 3856 then
(if i.val < 3848 then
(if i.val < 3844 then
(if i.val < 3842 then
(if i.val < 3841 then
[2, 1, 0, 3, 0, 1, 1, 0, 2]
else
[2, 1, 0, 3, 0, 2, 1, 0, 0])
else
(if i.val < 3843 then
[2, 1, 0, 3, 0, 2, 1, 0, 3]
else
[2, 1, 0, 3, 0, 2, 2, 1, 3]))
else
(if i.val < 3846 then
(if i.val < 3845 then
[2, 1, 0, 3, 0, 2, 2, 3, 3]
else
[2, 1, 0, 3, 2, 1, 1, 0, 0])
else
(if i.val < 3847 then
[2, 1, 0, 3, 2, 2, 1, 1, 3]
else
[2, 1, 0, 3, 2, 2, 3, 0, 1])))
else
(if i.val < 3852 then
(if i.val < 3850 then
(if i.val < 3849 then
[2, 1, 1, 0, 0, 2, 1, 1, 2]
else
[2, 1, 1, 0, 0, 2, 3, 3, 2])
else
(if i.val < 3851 then
[2, 1, 1, 0, 0, 3, 0, 1, 2]
else
[2, 1, 1, 0, 2, 3, 0, 0, 2]))
else
(if i.val < 3854 then
(if i.val < 3853 then
[2, 1, 1, 0, 2, 3, 0, 0, 3]
else
[2, 1, 1, 0, 2, 3, 0, 2, 1])
else
(if i.val < 3855 then
[2, 1, 1, 0, 2, 3, 2, 1, 1]
else
[2, 1, 1, 0, 3, 0, 0, 2, 3]))))
else
(if i.val < 3864 then
(if i.val < 3860 then
(if i.val < 3858 then
(if i.val < 3857 then
[2, 1, 1, 0, 3, 0, 1, 1, 2]
else
[2, 1, 1, 0, 3, 0, 1, 2, 1])
else
(if i.val < 3859 then
[2, 1, 1, 0, 3, 0, 2, 1, 1]
else
[2, 1, 1, 0, 3, 2, 1, 0, 0]))
else
(if i.val < 3862 then
(if i.val < 3861 then
[2, 1, 1, 0, 3, 3, 0, 1, 2]
else
[2, 1, 1, 0, 3, 3, 0, 2, 3])
else
(if i.val < 3863 then
[2, 1, 1, 3, 0, 1, 2, 2, 1]
else
[2, 1, 1, 3, 0, 2, 3, 3, 2])))
else
(if i.val < 3868 then
(if i.val < 3866 then
(if i.val < 3865 then
[2, 1, 1, 3, 2, 1, 0, 0, 3]
else
[2, 1, 1, 3, 3, 0, 1, 2, 1])
else
(if i.val < 3867 then
[2, 1, 1, 3, 3, 0, 1, 2, 3]
else
[2, 1, 3, 0, 0, 1, 2, 1, 1]))
else
(if i.val < 3870 then
(if i.val < 3869 then
[2, 1, 3, 0, 0, 1, 2, 2, 3]
else
[2, 1, 3, 0, 0, 3, 2, 2, 1])
else
(if i.val < 3871 then
[2, 1, 3, 0, 1, 2, 2, 1, 3]
else
[2, 1, 3, 0, 1, 2, 3, 0, 1])))))
else
(if i.val < 3888 then
(if i.val < 3880 then
(if i.val < 3876 then
(if i.val < 3874 then
(if i.val < 3873 then
[2, 1, 3, 3, 0, 2, 1, 1, 2]
else
[2, 2, 1, 0, 0, 3, 2, 2, 1])
else
(if i.val < 3875 then
[2, 2, 1, 0, 0, 3, 2, 2, 3]
else
[2, 2, 1, 0, 3, 0, 2, 1, 0]))
else
(if i.val < 3878 then
(if i.val < 3877 then
[2, 2, 1, 0, 3, 2, 1, 0, 0]
else
[2, 2, 1, 1, 0, 3, 0, 2, 3])
else
(if i.val < 3879 then
[2, 2, 1, 1, 3, 0, 1, 2, 1]
else
[2, 2, 1, 3, 0, 0, 1, 2, 2])))
else
(if i.val < 3884 then
(if i.val < 3882 then
(if i.val < 3881 then
[2, 2, 1, 3, 0, 0, 3, 2, 2]
else
[2, 2, 1, 3, 0, 1, 2, 3, 3])
else
(if i.val < 3883 then
[2, 2, 1, 3, 3, 0, 0, 2, 3]
else
[2, 2, 3, 0, 0, 1, 2, 2, 1]))
else
(if i.val < 3886 then
(if i.val < 3885 then
[2, 2, 3, 0, 0, 1, 2, 2, 3]
else
[2, 2, 3, 0, 0, 3, 2, 1, 0])
else
(if i.val < 3887 then
[2, 2, 3, 0, 0, 3, 2, 1, 1]
else
[2, 2, 3, 0, 1, 2, 1, 1, 3]))))
else
(if i.val < 3896 then
(if i.val < 3892 then
(if i.val < 3890 then
(if i.val < 3889 then
[2, 2, 3, 0, 1, 2, 1, 3, 3]
else
[2, 2, 3, 0, 1, 2, 3, 0, 1])
else
(if i.val < 3891 then
[2, 2, 3, 0, 1, 2, 3, 3, 0]
else
[2, 2, 3, 0, 2, 3, 3, 0, 2]))
else
(if i.val < 3894 then
(if i.val < 3893 then
[2, 2, 3, 2, 1, 0, 3, 2, 2]
else
[2, 2, 3, 2, 2, 1, 3, 0, 0])
else
(if i.val < 3895 then
[2, 2, 3, 2, 2, 3, 0, 1, 1]
else
[2, 2, 3, 2, 2, 3, 0, 1, 2])))
else
(if i.val < 3900 then
(if i.val < 3898 then
(if i.val < 3897 then
[2, 3, 0, 0, 1, 1, 2, 1, 1]
else
[2, 3, 0, 0, 1, 1, 2, 1, 3])
else
(if i.val < 3899 then
[2, 3, 0, 0, 1, 1, 2, 2, 1]
else
[2, 3, 0, 0, 1, 2, 3, 0, 1]))
else
(if i.val < 3902 then
(if i.val < 3901 then
[2, 3, 0, 0, 2, 3, 2, 1, 1]
else
[2, 3, 0, 0, 2, 3, 3, 2, 1])
else
(if i.val < 3903 then
[2, 3, 0, 0, 3, 2, 1, 1, 2]
else
[2, 3, 0, 0, 3, 2, 2, 1, 3]))))))
else
(if i.val < 3936 then
(if i.val < 3920 then
(if i.val < 3912 then
(if i.val < 3908 then
(if i.val < 3906 then
(if i.val < 3905 then
[2, 3, 0, 1, 1, 0, 2, 3, 3]
else
[2, 3, 0, 1, 1, 0, 3, 2, 1])
else
(if i.val < 3907 then
[2, 3, 0, 1, 1, 2, 1, 0, 3]
else
[2, 3, 0, 1, 1, 2, 2, 1, 1]))
else
(if i.val < 3910 then
(if i.val < 3909 then
[2, 3, 0, 1, 1, 2, 3, 3, 0]
else
[2, 3, 0, 1, 2, 1, 1, 3, 3])
else
(if i.val < 3911 then
[2, 3, 0, 1, 2, 2, 1, 3, 3]
else
[2, 3, 0, 2, 1, 1, 2, 3, 0])))
else
(if i.val < 3916 then
(if i.val < 3914 then
(if i.val < 3913 then
[2, 3, 0, 2, 1, 1, 2, 3, 3]
else
[2, 3, 0, 2, 2, 1, 3, 3, 2])
else
(if i.val < 3915 then
[2, 3, 0, 2, 3, 3, 2, 1, 0]
else
[2, 3, 0, 2, 3, 3, 2, 1, 1]))
else
(if i.val < 3918 then
(if i.val < 3917 then
[2, 3, 2, 1, 0, 0, 1, 2, 2]
else
[2, 3, 2, 1, 0, 0, 3, 2, 2])
else
(if i.val < 3919 then
[2, 3, 2, 1, 0, 3, 2, 1, 1]
else
[2, 3, 2, 1, 0, 3, 2, 2, 1]))))
else
(if i.val < 3928 then
(if i.val < 3924 then
(if i.val < 3922 then
(if i.val < 3921 then
[2, 3, 2, 1, 1, 0, 2, 3, 2]
else
[2, 3, 2, 1, 1, 0, 3, 2, 1])
else
(if i.val < 3923 then
[2, 3, 2, 2, 1, 0, 3, 2, 2]
else
[2, 3, 2, 2, 1, 3, 0, 1, 2]))
else
(if i.val < 3926 then
(if i.val < 3925 then
[2, 3, 3, 0, 1, 1, 0, 2, 3]
else
[2, 3, 3, 0, 1, 2, 1, 0, 0])
else
(if i.val < 3927 then
[2, 3, 3, 0, 1, 2, 1, 1, 0]
else
[2, 3, 3, 0, 1, 2, 2, 1, 0])))
else
(if i.val < 3932 then
(if i.val < 3930 then
(if i.val < 3929 then
[2, 3, 3, 0, 2, 3, 3, 0, 2]
else
[3, 0, 0, 1, 1, 2, 2, 1, 0])
else
(if i.val < 3931 then
[3, 0, 0, 1, 1, 2, 3, 0, 1]
else
[3, 0, 0, 1, 2, 1, 0, 3, 0]))
else
(if i.val < 3934 then
(if i.val < 3933 then
[3, 0, 0, 1, 2, 1, 1, 3, 0]
else
[3, 0, 0, 1, 2, 2, 3, 0, 0])
else
(if i.val < 3935 then
[3, 0, 0, 1, 2, 2, 3, 2, 1]
else
[3, 0, 0, 2, 2, 3, 0, 2, 2])))))
else
(if i.val < 3952 then
(if i.val < 3944 then
(if i.val < 3940 then
(if i.val < 3938 then
(if i.val < 3937 then
[3, 0, 0, 2, 2, 3, 2, 1, 1]
else
[3, 0, 0, 2, 2, 3, 2, 2, 1])
else
(if i.val < 3939 then
[3, 0, 0, 2, 3, 2, 1, 0, 0]
else
[3, 0, 0, 3, 2, 1, 1, 0, 2]))
else
(if i.val < 3942 then
(if i.val < 3941 then
[3, 0, 0, 3, 2, 1, 1, 2, 3]
else
[3, 0, 1, 1, 0, 2, 1, 0, 0])
else
(if i.val < 3943 then
[3, 0, 1, 1, 0, 2, 1, 1, 2]
else
[3, 0, 1, 1, 0, 3, 2, 1, 1])))
else
(if i.val < 3948 then
(if i.val < 3946 then
(if i.val < 3945 then
[3, 0, 1, 2, 1, 0, 3, 0, 1]
else
[3, 0, 1, 2, 1, 1, 0, 2, 3])
else
(if i.val < 3947 then
[3, 0, 1, 2, 1, 3, 0, 1, 1]
else
[3, 0, 1, 2, 1, 3, 0, 1, 2]))
else
(if i.val < 3950 then
(if i.val < 3949 then
[3, 0, 1, 2, 1, 3, 3, 2, 2]
else
[3, 0, 1, 2, 2, 3, 3, 0, 0])
else
(if i.val < 3951 then
[3, 0, 1, 2, 3, 3, 0, 1, 2]
else
[3, 0, 1, 2, 3, 3, 2, 1, 1]))))
else
(if i.val < 3960 then
(if i.val < 3956 then
(if i.val < 3954 then
(if i.val < 3953 then
[3, 0, 2, 1, 0, 3, 3, 2, 1]
else
[3, 0, 2, 1, 1, 0, 0, 2, 1])
else
(if i.val < 3955 then
[3, 0, 2, 1, 1, 0, 0, 2, 3]
else
[3, 0, 2, 1, 1, 0, 3, 2, 1]))
else
(if i.val < 3958 then
(if i.val < 3957 then
[3, 0, 2, 1, 1, 2, 3, 3, 0]
else
[3, 0, 2, 1, 1, 3, 2, 2, 3])
else
(if i.val < 3959 then
[3, 0, 2, 1, 3, 3, 2, 2, 1]
else
[3, 0, 2, 3, 3, 0, 2, 1, 1])))
else
(if i.val < 3964 then
(if i.val < 3962 then
(if i.val < 3961 then
[3, 0, 2, 3, 3, 0, 2, 1, 3]
else
[3, 0, 2, 3, 3, 2, 1, 0, 0])
else
(if i.val < 3963 then
[3, 2, 1, 0, 0, 3, 2, 2, 1]
else
[3, 2, 1, 0, 3, 2, 1, 0, 0]))
else
(if i.val < 3966 then
(if i.val < 3965 then
[3, 2, 1, 0, 3, 2, 2, 1, 3]
else
[3, 2, 1, 1, 0, 2, 1, 1, 2])
else
(if i.val < 3967 then
[3, 2, 1, 1, 0, 2, 1, 3, 3]
else
[3, 2, 1, 1, 0, 2, 3, 0, 2])))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row18_cosetWordsPart0031 : Fin 4320 → List (Fin 4) :=
  fun i => (if i.val < 4032 then
(if i.val < 4000 then
(if i.val < 3984 then
(if i.val < 3976 then
(if i.val < 3972 then
(if i.val < 3970 then
(if i.val < 3969 then
[3, 2, 1, 1, 0, 2, 3, 2, 1]
else
[3, 2, 1, 1, 0, 2, 3, 3, 2])
else
(if i.val < 3971 then
[3, 2, 2, 1, 0, 0, 1, 2, 3]
else
[3, 2, 2, 1, 3, 0, 0, 3, 2]))
else
(if i.val < 3974 then
(if i.val < 3973 then
[3, 2, 2, 3, 0, 1, 2, 3, 3]
else
[3, 3, 0, 0, 2, 1, 1, 2, 3])
else
(if i.val < 3975 then
[3, 3, 0, 1, 1, 2, 3, 3, 2]
else
[3, 3, 0, 1, 2, 1, 1, 0, 2])))
else
(if i.val < 3980 then
(if i.val < 3978 then
(if i.val < 3977 then
[3, 3, 0, 1, 2, 1, 3, 0, 1]
else
[3, 3, 0, 1, 2, 1, 3, 3, 0])
else
(if i.val < 3979 then
[3, 3, 0, 1, 2, 3, 0, 0, 3]
else
[3, 3, 0, 1, 2, 3, 0, 1, 1]))
else
(if i.val < 3982 then
(if i.val < 3981 then
[3, 3, 0, 2, 1, 0, 3, 3, 2]
else
[3, 3, 0, 2, 1, 1, 0, 2, 1])
else
(if i.val < 3983 then
[3, 3, 0, 2, 1, 1, 0, 3, 2]
else
[3, 3, 2, 1, 0, 3, 2, 2, 1]))))
else
(if i.val < 3992 then
(if i.val < 3988 then
(if i.val < 3986 then
(if i.val < 3985 then
[3, 3, 2, 1, 0, 3, 2, 2, 3]
else
[3, 3, 2, 1, 0, 3, 3, 0, 1])
else
(if i.val < 3987 then
[3, 3, 2, 1, 1, 0, 2, 3, 2]
else
[3, 3, 2, 2, 1, 0, 3, 2, 1]))
else
(if i.val < 3990 then
(if i.val < 3989 then
[0, 0, 1, 0, 0, 1, 2, 1, 1, 2]
else
[0, 0, 1, 0, 0, 2, 1, 1, 2, 3])
else
(if i.val < 3991 then
[0, 0, 1, 0, 0, 3, 3, 0, 2, 1]
else
[0, 0, 1, 0, 2, 2, 1, 0, 3, 2])))
else
(if i.val < 3996 then
(if i.val < 3994 then
(if i.val < 3993 then
[0, 0, 1, 0, 2, 2, 1, 0, 3, 3]
else
[0, 0, 1, 0, 2, 2, 1, 3, 3, 2])
else
(if i.val < 3995 then
[0, 0, 1, 0, 2, 2, 3, 0, 2, 1]
else
[0, 0, 1, 0, 2, 3, 0, 1, 2, 1]))
else
(if i.val < 3998 then
(if i.val < 3997 then
[0, 0, 1, 0, 2, 3, 0, 1, 2, 2]
else
[0, 0, 1, 0, 2, 3, 2, 1, 1, 0])
else
(if i.val < 3999 then
[0, 0, 1, 0, 2, 3, 3, 0, 1, 2]
else
[0, 0, 1, 0, 3, 0, 0, 2, 1, 1])))))
else
(if i.val < 4016 then
(if i.val < 4008 then
(if i.val < 4004 then
(if i.val < 4002 then
(if i.val < 4001 then
[0, 0, 1, 0, 3, 0, 0, 2, 3, 2]
else
[0, 0, 1, 0, 3, 2, 1, 0, 3, 2])
else
(if i.val < 4003 then
[0, 0, 1, 0, 3, 3, 0, 1, 2, 1]
else
[0, 0, 1, 1, 0, 0, 2, 1, 0, 0]))
else
(if i.val < 4006 then
(if i.val < 4005 then
[0, 0, 1, 1, 0, 0, 2, 3, 0, 1]
else
[0, 0, 1, 1, 0, 3, 2, 1, 1, 2])
else
(if i.val < 4007 then
[0, 0, 1, 1, 0, 3, 2, 2, 1, 0]
else
[0, 0, 1, 1, 2, 1, 1, 0, 3, 2])))
else
(if i.val < 4012 then
(if i.val < 4010 then
(if i.val < 4009 then
[0, 0, 1, 1, 2, 1, 1, 3, 0, 1]
else
[0, 0, 1, 1, 2, 2, 3, 2, 1, 0])
else
(if i.val < 4011 then
[0, 0, 1, 1, 2, 3, 2, 1, 0, 3]
else
[0, 0, 1, 1, 3, 0, 1, 1, 2, 3]))
else
(if i.val < 4014 then
(if i.val < 4013 then
[0, 0, 1, 1, 3, 0, 2, 3, 3, 2]
else
[0, 0, 1, 2, 1, 1, 2, 3, 0, 0])
else
(if i.val < 4015 then
[0, 0, 1, 2, 1, 3, 0, 1, 2, 2]
else
[0, 0, 1, 2, 1, 3, 2, 2, 1, 3]))))
else
(if i.val < 4024 then
(if i.val < 4020 then
(if i.val < 4018 then
(if i.val < 4017 then
[0, 0, 1, 2, 1, 3, 3, 0, 1, 2]
else
[0, 0, 1, 2, 1, 3, 3, 0, 2, 2])
else
(if i.val < 4019 then
[0, 0, 1, 2, 1, 3, 3, 2, 2, 1]
else
[0, 0, 1, 2, 2, 1, 0, 3, 0, 2]))
else
(if i.val < 4022 then
(if i.val < 4021 then
[0, 0, 1, 2, 2, 1, 0, 3, 2, 1]
else
[0, 0, 1, 2, 2, 3, 0, 0, 3, 2])
else
(if i.val < 4023 then
[0, 0, 1, 2, 2, 3, 0, 2, 2, 1]
else
[0, 0, 1, 2, 2, 3, 2, 2, 1, 3])))
else
(if i.val < 4028 then
(if i.val < 4026 then
(if i.val < 4025 then
[0, 0, 1, 2, 3, 0, 0, 1, 2, 1]
else
[0, 0, 1, 2, 3, 0, 1, 2, 2, 1])
else
(if i.val < 4027 then
[0, 0, 1, 2, 3, 0, 1, 2, 2, 3]
else
[0, 0, 1, 2, 3, 0, 1, 2, 3, 0]))
else
(if i.val < 4030 then
(if i.val < 4029 then
[0, 0, 1, 2, 3, 0, 2, 1, 1, 2]
else
[0, 0, 1, 2, 3, 3, 0, 1, 1, 2])
else
(if i.val < 4031 then
[0, 0, 1, 2, 3, 3, 0, 1, 2, 2]
else
[0, 0, 1, 2, 3, 3, 2, 1, 0, 3]))))))
else
(if i.val < 4064 then
(if i.val < 4048 then
(if i.val < 4040 then
(if i.val < 4036 then
(if i.val < 4034 then
(if i.val < 4033 then
[0, 0, 1, 3, 0, 0, 1, 1, 2, 3]
else
[0, 0, 1, 3, 0, 0, 1, 2, 1, 1])
else
(if i.val < 4035 then
[0, 0, 1, 3, 0, 1, 1, 2, 2, 3]
else
[0, 0, 1, 3, 2, 1, 1, 0, 0, 2]))
else
(if i.val < 4038 then
(if i.val < 4037 then
[0, 0, 1, 3, 3, 0, 2, 1, 1, 2]
else
[0, 0, 2, 1, 1, 0, 0, 2, 1, 3])
else
(if i.val < 4039 then
[0, 0, 2, 1, 1, 0, 0, 2, 3, 0]
else
[0, 0, 2, 1, 1, 0, 2, 1, 1, 2])))
else
(if i.val < 4044 then
(if i.val < 4042 then
(if i.val < 4041 then
[0, 0, 2, 1, 1, 0, 2, 3, 2, 1]
else
[0, 0, 2, 1, 1, 0, 3, 0, 2, 1])
else
(if i.val < 4043 then
[0, 0, 2, 1, 1, 0, 3, 0, 2, 2]
else
[0, 0, 2, 1, 1, 0, 3, 0, 2, 3]))
else
(if i.val < 4046 then
(if i.val < 4045 then
[0, 0, 2, 1, 1, 2, 3, 2, 1, 0]
else
[0, 0, 2, 1, 1, 3, 2, 2, 1, 0])
else
(if i.val < 4047 then
[0, 0, 2, 1, 1, 3, 2, 2, 3, 0]
else
[0, 0, 2, 1, 3, 0, 0, 1, 2, 2]))))
else
(if i.val < 4056 then
(if i.val < 4052 then
(if i.val < 4050 then
(if i.val < 4049 then
[0, 0, 2, 1, 3, 3, 0, 0, 2, 3]
else
[0, 0, 2, 2, 1, 0, 0, 1, 3, 2])
else
(if i.val < 4051 then
[0, 0, 2, 2, 1, 3, 0, 0, 3, 2]
else
[0, 0, 2, 2, 3, 0, 1, 2, 3, 3]))
else
(if i.val < 4054 then
(if i.val < 4053 then
[0, 0, 2, 2, 3, 0, 2, 2, 1, 3]
else
[0, 0, 2, 3, 0, 0, 1, 1, 2, 3])
else
(if i.val < 4055 then
[0, 0, 2, 3, 0, 0, 2, 3, 3, 2]
else
[0, 0, 2, 3, 0, 1, 2, 2, 3, 0])))
else
(if i.val < 4060 then
(if i.val < 4058 then
(if i.val < 4057 then
[0, 0, 2, 3, 2, 1, 0, 3, 2, 2]
else
[0, 0, 2, 3, 2, 2, 3, 0, 1, 2])
else
(if i.val < 4059 then
[0, 0, 2, 3, 3, 0, 0, 2, 1, 3]
else
[0, 0, 2, 3, 3, 0, 1, 2, 1, 3]))
else
(if i.val < 4062 then
(if i.val < 4061 then
[0, 0, 3, 0, 0, 1, 1, 2, 1, 3]
else
[0, 0, 3, 0, 0, 1, 2, 3, 3, 2])
else
(if i.val < 4063 then
[0, 0, 3, 0, 0, 2, 2, 3, 2, 2]
else
[0, 0, 3, 0, 0, 2, 3, 3, 2, 1])))))
else
(if i.val < 4080 then
(if i.val < 4072 then
(if i.val < 4068 then
(if i.val < 4066 then
(if i.val < 4065 then
[0, 0, 3, 0, 0, 3, 2, 1, 0, 0]
else
[0, 0, 3, 0, 1, 2, 3, 0, 1, 1])
else
(if i.val < 4067 then
[0, 0, 3, 0, 1, 2, 3, 3, 0, 1]
else
[0, 0, 3, 0, 2, 1, 1, 0, 3, 2]))
else
(if i.val < 4070 then
(if i.val < 4069 then
[0, 0, 3, 0, 2, 2, 1, 0, 3, 3]
else
[0, 0, 3, 2, 1, 0, 0, 1, 2, 2])
else
(if i.val < 4071 then
[0, 0, 3, 2, 1, 0, 3, 2, 2, 3]
else
[0, 0, 3, 2, 1, 1, 0, 3, 2, 1])))
else
(if i.val < 4076 then
(if i.val < 4074 then
(if i.val < 4073 then
[0, 0, 3, 2, 1, 1, 2, 3, 0, 1]
else
[0, 0, 3, 2, 2, 1, 3, 0, 1, 2])
else
(if i.val < 4075 then
[0, 0, 3, 3, 0, 1, 2, 1, 1, 0]
else
[0, 0, 3, 3, 2, 1, 0, 3, 2, 2]))
else
(if i.val < 4078 then
(if i.val < 4077 then
[0, 1, 0, 0, 1, 2, 1, 0, 0, 3]
else
[0, 1, 0, 0, 1, 2, 2, 3, 2, 1])
else
(if i.val < 4079 then
[0, 1, 0, 0, 1, 2, 3, 0, 0, 3]
else
[0, 1, 0, 0, 2, 1, 1, 2, 3, 0]))))
else
(if i.val < 4088 then
(if i.val < 4084 then
(if i.val < 4082 then
(if i.val < 4081 then
[0, 1, 0, 0, 2, 1, 3, 3, 2, 2]
else
[0, 1, 0, 0, 2, 2, 1, 0, 3, 2])
else
(if i.val < 4083 then
[0, 1, 0, 0, 3, 0, 0, 1, 1, 2]
else
[0, 1, 0, 0, 3, 2, 1, 1, 2, 3]))
else
(if i.val < 4086 then
(if i.val < 4085 then
[0, 1, 0, 0, 3, 3, 2, 1, 0, 3]
else
[0, 1, 0, 2, 1, 0, 3, 3, 0, 1])
else
(if i.val < 4087 then
[0, 1, 0, 2, 1, 1, 2, 3, 3, 0]
else
[0, 1, 0, 2, 1, 3, 3, 0, 1, 2])))
else
(if i.val < 4092 then
(if i.val < 4090 then
(if i.val < 4089 then
[0, 1, 0, 2, 1, 3, 3, 2, 2, 1]
else
[0, 1, 0, 2, 2, 1, 3, 3, 0, 2])
else
(if i.val < 4091 then
[0, 1, 0, 2, 2, 3, 0, 2, 2, 1]
else
[0, 1, 0, 2, 3, 0, 1, 1, 2, 3]))
else
(if i.val < 4094 then
(if i.val < 4093 then
[0, 1, 0, 2, 3, 3, 0, 1, 2, 1]
else
[0, 1, 0, 2, 3, 3, 2, 1, 0, 3])
else
(if i.val < 4095 then
[0, 1, 0, 3, 0, 0, 1, 2, 1, 1]
else
[0, 1, 0, 3, 0, 0, 1, 2, 3, 3])))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row18_cosetWordsPart0032 : Fin 4320 → List (Fin 4) :=
  fun i => (if i.val < 4160 then
(if i.val < 4128 then
(if i.val < 4112 then
(if i.val < 4104 then
(if i.val < 4100 then
(if i.val < 4098 then
(if i.val < 4097 then
[0, 1, 0, 3, 2, 2, 1, 0, 3, 2]
else
[0, 1, 0, 3, 2, 2, 3, 0, 1, 2])
else
(if i.val < 4099 then
[0, 1, 0, 3, 3, 0, 1, 2, 1, 0]
else
[0, 1, 0, 3, 3, 0, 1, 2, 2, 1]))
else
(if i.val < 4102 then
(if i.val < 4101 then
[0, 1, 0, 3, 3, 0, 1, 2, 2, 3]
else
[0, 1, 0, 3, 3, 0, 2, 3, 3, 2])
else
(if i.val < 4103 then
[0, 1, 1, 0, 2, 1, 0, 3, 3, 2]
else
[0, 1, 1, 0, 2, 1, 1, 0, 2, 1])))
else
(if i.val < 4108 then
(if i.val < 4106 then
(if i.val < 4105 then
[0, 1, 1, 0, 2, 1, 1, 0, 2, 3]
else
[0, 1, 1, 0, 2, 1, 1, 0, 3, 2])
else
(if i.val < 4107 then
[0, 1, 1, 0, 2, 1, 1, 2, 3, 3]
else
[0, 1, 1, 0, 2, 1, 1, 3, 0, 2]))
else
(if i.val < 4110 then
(if i.val < 4109 then
[0, 1, 1, 0, 2, 1, 3, 3, 2, 2]
else
[0, 1, 1, 0, 2, 3, 2, 1, 0, 3])
else
(if i.val < 4111 then
[0, 1, 1, 0, 3, 0, 0, 2, 1, 1]
else
[0, 1, 1, 0, 3, 0, 1, 2, 3, 3]))))
else
(if i.val < 4120 then
(if i.val < 4116 then
(if i.val < 4114 then
(if i.val < 4113 then
[0, 1, 1, 0, 3, 0, 2, 1, 0, 0]
else
[0, 1, 1, 0, 3, 2, 1, 0, 0, 3])
else
(if i.val < 4115 then
[0, 1, 1, 0, 3, 2, 1, 1, 2, 3]
else
[0, 1, 1, 0, 3, 2, 2, 1, 1, 3]))
else
(if i.val < 4118 then
(if i.val < 4117 then
[0, 1, 1, 0, 3, 2, 2, 3, 0, 1]
else
[0, 1, 1, 0, 3, 3, 0, 1, 2, 2])
else
(if i.val < 4119 then
[0, 1, 1, 2, 1, 0, 3, 3, 0, 1]
else
[0, 1, 1, 2, 1, 1, 0, 2, 3, 2])))
else
(if i.val < 4124 then
(if i.val < 4122 then
(if i.val < 4121 then
[0, 1, 1, 2, 1, 1, 2, 3, 0, 1]
else
[0, 1, 1, 2, 1, 3, 3, 2, 2, 1])
else
(if i.val < 4123 then
[0, 1, 1, 2, 2, 1, 0, 3, 2, 1]
else
[0, 1, 1, 2, 2, 3, 2, 2, 1, 3]))
else
(if i.val < 4126 then
(if i.val < 4125 then
[0, 1, 1, 2, 3, 0, 1, 1, 2, 1]
else
[0, 1, 1, 2, 3, 0, 1, 2, 2, 1])
else
(if i.val < 4127 then
[0, 1, 1, 2, 3, 0, 1, 2, 2, 3]
else
[0, 1, 1, 2, 3, 0, 1, 2, 3, 0])))))
else
(if i.val < 4144 then
(if i.val < 4136 then
(if i.val < 4132 then
(if i.val < 4130 then
(if i.val < 4129 then
[0, 1, 1, 2, 3, 3, 0, 1, 1, 2]
else
[0, 1, 1, 2, 3, 3, 2, 1, 0, 3])
else
(if i.val < 4131 then
[0, 1, 1, 3, 0, 1, 1, 0, 2, 1]
else
[0, 1, 1, 3, 0, 1, 1, 2, 2, 3]))
else
(if i.val < 4134 then
(if i.val < 4133 then
[0, 1, 1, 3, 2, 2, 1, 0, 3, 2]
else
[0, 1, 1, 3, 3, 0, 2, 3, 3, 2])
else
(if i.val < 4135 then
[0, 1, 2, 1, 0, 0, 3, 2, 2, 1]
else
[0, 1, 2, 1, 1, 0, 2, 3, 0, 0])))
else
(if i.val < 4140 then
(if i.val < 4138 then
(if i.val < 4137 then
[0, 1, 2, 1, 1, 0, 2, 3, 0, 1]
else
[0, 1, 2, 1, 1, 3, 2, 2, 3, 0])
else
(if i.val < 4139 then
[0, 1, 2, 1, 3, 0, 0, 3, 2, 2]
else
[0, 1, 2, 1, 3, 0, 1, 2, 3, 0]))
else
(if i.val < 4142 then
(if i.val < 4141 then
[0, 1, 2, 1, 3, 3, 2, 2, 1, 1]
else
[0, 1, 2, 2, 1, 0, 3, 0, 2, 1])
else
(if i.val < 4143 then
[0, 1, 2, 2, 1, 1, 3, 2, 1, 0]
else
[0, 1, 2, 2, 3, 0, 1, 2, 3, 3]))))
else
(if i.val < 4152 then
(if i.val < 4148 then
(if i.val < 4146 then
(if i.val < 4145 then
[0, 1, 2, 2, 3, 0, 2, 2, 1, 3]
else
[0, 1, 2, 2, 3, 2, 2, 1, 1, 3])
else
(if i.val < 4147 then
[0, 1, 2, 3, 0, 0, 3, 2, 2, 1]
else
[0, 1, 2, 3, 0, 1, 1, 2, 1, 1]))
else
(if i.val < 4150 then
(if i.val < 4149 then
[0, 1, 2, 3, 0, 1, 2, 2, 1, 3]
else
[0, 1, 2, 3, 0, 1, 2, 2, 3, 0])
else
(if i.val < 4151 then
[0, 1, 2, 3, 2, 1, 0, 3, 2, 2]
else
[0, 1, 2, 3, 2, 2, 1, 3, 2, 2])))
else
(if i.val < 4156 then
(if i.val < 4154 then
(if i.val < 4153 then
[0, 1, 2, 3, 3, 0, 1, 2, 1, 0]
else
[0, 1, 2, 3, 3, 0, 1, 2, 1, 3])
else
(if i.val < 4155 then
[0, 1, 2, 3, 3, 0, 1, 2, 3, 3]
else
[0, 1, 3, 0, 0, 1, 2, 3, 3, 2]))
else
(if i.val < 4158 then
(if i.val < 4157 then
[0, 1, 3, 2, 1, 1, 0, 0, 3, 2]
else
[0, 1, 3, 2, 2, 1, 0, 3, 2, 1])
else
(if i.val < 4159 then
[0, 1, 3, 2, 2, 3, 0, 0, 1, 2]
else
[0, 1, 3, 3, 0, 0, 2, 3, 3, 2]))))))
else
(if i.val < 4192 then
(if i.val < 4176 then
(if i.val < 4168 then
(if i.val < 4164 then
(if i.val < 4162 then
(if i.val < 4161 then
[0, 1, 3, 3, 0, 1, 2, 2, 1, 0]
else
[0, 1, 3, 3, 0, 2, 1, 1, 2, 3])
else
(if i.val < 4163 then
[0, 2, 1, 1, 0, 2, 3, 0, 0, 3]
else
[0, 2, 1, 1, 0, 3, 0, 1, 2, 1]))
else
(if i.val < 4166 then
(if i.val < 4165 then
[0, 2, 1, 1, 0, 3, 3, 0, 2, 3]
else
[0, 2, 1, 1, 3, 0, 2, 3, 3, 2])
else
(if i.val < 4167 then
[0, 2, 1, 3, 0, 0, 1, 2, 2, 3]
else
[0, 2, 1, 3, 3, 0, 2, 1, 1, 2])))
else
(if i.val < 4172 then
(if i.val < 4170 then
(if i.val < 4169 then
[0, 2, 2, 1, 3, 3, 0, 0, 2, 3]
else
[0, 2, 2, 3, 2, 1, 0, 3, 2, 2])
else
(if i.val < 4171 then
[0, 2, 2, 3, 2, 2, 1, 3, 0, 0]
else
[0, 2, 3, 0, 0, 1, 1, 2, 1, 3]))
else
(if i.val < 4174 then
(if i.val < 4173 then
[0, 2, 3, 0, 0, 2, 3, 3, 2, 1]
else
[0, 2, 3, 0, 1, 1, 0, 2, 3, 3])
else
(if i.val < 4175 then
[0, 2, 3, 0, 1, 1, 0, 3, 2, 1]
else
[0, 2, 3, 0, 1, 1, 2, 2, 1, 1]))))
else
(if i.val < 4184 then
(if i.val < 4180 then
(if i.val < 4178 then
(if i.val < 4177 then
[0, 2, 3, 0, 2, 1, 1, 2, 3, 0]
else
[0, 2, 3, 2, 1, 0, 0, 1, 2, 2])
else
(if i.val < 4179 then
[0, 2, 3, 2, 1, 1, 0, 2, 3, 2]
else
[0, 2, 3, 2, 1, 1, 0, 3, 2, 1]))
else
(if i.val < 4182 then
(if i.val < 4181 then
[0, 2, 3, 2, 2, 1, 3, 0, 1, 2]
else
[0, 2, 3, 3, 0, 1, 1, 0, 2, 3])
else
(if i.val < 4183 then
[0, 2, 3, 3, 0, 2, 3, 3, 0, 2]
else
[0, 3, 0, 0, 1, 1, 2, 2, 1, 0])))
else
(if i.val < 4188 then
(if i.val < 4186 then
(if i.val < 4185 then
[0, 3, 0, 0, 2, 2, 3, 2, 1, 1]
else
[0, 3, 0, 0, 2, 2, 3, 2, 2, 1])
else
(if i.val < 4187 then
[0, 3, 0, 1, 1, 0, 2, 1, 0, 0]
else
[0, 3, 0, 1, 1, 0, 2, 1, 1, 2]))
else
(if i.val < 4190 then
(if i.val < 4189 then
[0, 3, 0, 1, 2, 1, 1, 0, 2, 3]
else
[0, 3, 0, 1, 2, 3, 3, 0, 1, 2])
else
(if i.val < 4191 then
[0, 3, 0, 1, 2, 3, 3, 2, 1, 1]
else
[0, 3, 0, 2, 1, 1, 0, 0, 2, 1])))))
else
(if i.val < 4208 then
(if i.val < 4200 then
(if i.val < 4196 then
(if i.val < 4194 then
(if i.val < 4193 then
[0, 3, 0, 2, 1, 1, 0, 0, 2, 3]
else
[0, 3, 0, 2, 1, 1, 0, 3, 2, 1])
else
(if i.val < 4195 then
[0, 3, 0, 2, 1, 1, 3, 2, 2, 3]
else
[0, 3, 0, 2, 1, 3, 3, 2, 2, 1]))
else
(if i.val < 4198 then
(if i.val < 4197 then
[0, 3, 0, 2, 3, 3, 0, 2, 1, 3]
else
[0, 3, 2, 1, 0, 3, 2, 1, 0, 0])
else
(if i.val < 4199 then
[0, 3, 2, 1, 1, 0, 2, 3, 0, 2]
else
[0, 3, 2, 1, 1, 0, 2, 3, 2, 1])))
else
(if i.val < 4204 then
(if i.val < 4202 then
(if i.val < 4201 then
[0, 3, 2, 2, 1, 3, 0, 0, 3, 2]
else
[0, 3, 2, 2, 3, 0, 1, 2, 3, 3])
else
(if i.val < 4203 then
[0, 3, 3, 0, 1, 1, 2, 3, 3, 2]
else
[0, 3, 3, 2, 1, 0, 3, 2, 2, 3]))
else
(if i.val < 4206 then
(if i.val < 4205 then
[0, 3, 3, 2, 1, 0, 3, 3, 0, 1]
else
[0, 3, 3, 2, 1, 1, 0, 2, 3, 2])
else
(if i.val < 4207 then
[1, 0, 0, 1, 2, 1, 1, 2, 3, 0]
else
[1, 0, 0, 1, 2, 1, 3, 3, 2, 2]))))
else
(if i.val < 4216 then
(if i.val < 4212 then
(if i.val < 4210 then
(if i.val < 4209 then
[1, 0, 0, 1, 2, 3, 0, 1, 1, 2]
else
[1, 0, 0, 1, 2, 3, 3, 0, 2, 2])
else
(if i.val < 4211 then
[1, 0, 0, 1, 3, 0, 0, 3, 2, 1]
else
[1, 0, 0, 2, 1, 1, 0, 2, 1, 3]))
else
(if i.val < 4214 then
(if i.val < 4213 then
[1, 0, 0, 2, 1, 1, 2, 3, 0, 1]
else
[1, 0, 0, 3, 0, 0, 2, 3, 3, 2])
else
(if i.val < 4215 then
[1, 0, 0, 3, 3, 0, 1, 2, 2, 3]
else
[1, 0, 2, 2, 1, 3, 3, 2, 1, 0])))
else
(if i.val < 4220 then
(if i.val < 4218 then
(if i.val < 4217 then
[1, 0, 2, 2, 3, 0, 1, 2, 3, 3]
else
[1, 0, 2, 2, 3, 0, 2, 2, 1, 3])
else
(if i.val < 4219 then
[1, 0, 2, 2, 3, 0, 2, 3, 3, 0]
else
[1, 0, 2, 2, 3, 2, 2, 1, 1, 3]))
else
(if i.val < 4222 then
(if i.val < 4221 then
[1, 0, 2, 2, 3, 2, 2, 3, 0, 0]
else
[1, 0, 2, 3, 0, 1, 1, 0, 2, 1])
else
(if i.val < 4223 then
[1, 0, 2, 3, 0, 1, 1, 2, 1, 1]
else
[1, 0, 2, 3, 3, 0, 1, 1, 0, 2])))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row18_cosetWordsPart0033 : Fin 4320 → List (Fin 4) :=
  fun i => (if i.val < 4272 then
(if i.val < 4248 then
(if i.val < 4236 then
(if i.val < 4230 then
(if i.val < 4227 then
(if i.val < 4225 then
[1, 0, 2, 3, 3, 0, 1, 2, 1, 1]
else
(if i.val < 4226 then
[1, 0, 2, 3, 3, 0, 1, 2, 1, 3]
else
[1, 0, 2, 3, 3, 0, 2, 3, 3, 2]))
else
(if i.val < 4228 then
[1, 0, 3, 0, 0, 2, 1, 1, 0, 2]
else
(if i.val < 4229 then
[1, 0, 3, 0, 0, 3, 2, 1, 1, 0]
else
[1, 0, 3, 0, 0, 3, 2, 1, 1, 2])))
else
(if i.val < 4233 then
(if i.val < 4231 then
[1, 0, 3, 0, 2, 3, 3, 2, 1, 0]
else
(if i.val < 4232 then
[1, 0, 3, 2, 1, 0, 0, 1, 2, 2]
else
[1, 0, 3, 2, 2, 1, 0, 0, 1, 3]))
else
(if i.val < 4234 then
[1, 0, 3, 2, 2, 3, 0, 0, 3, 2]
else
(if i.val < 4235 then
[1, 0, 3, 3, 0, 1, 1, 0, 2, 3]
else
[1, 0, 3, 3, 2, 1, 0, 3, 2, 2]))))
else
(if i.val < 4242 then
(if i.val < 4239 then
(if i.val < 4237 then
[1, 1, 0, 0, 3, 0, 1, 2, 3, 3]
else
(if i.val < 4238 then
[1, 1, 0, 2, 1, 1, 0, 3, 2, 1]
else
[1, 1, 0, 2, 2, 3, 2, 2, 1, 3]))
else
(if i.val < 4240 then
[1, 1, 0, 2, 3, 2, 1, 1, 0, 0]
else
(if i.val < 4241 then
[1, 1, 0, 3, 0, 2, 1, 0, 3, 3]
else
[1, 1, 0, 3, 0, 2, 3, 3, 2, 1])))
else
(if i.val < 4245 then
(if i.val < 4243 then
[1, 1, 0, 3, 2, 1, 1, 2, 3, 0]
else
(if i.val < 4244 then
[1, 1, 0, 3, 3, 0, 1, 2, 2, 1]
else
[1, 1, 2, 1, 0, 3, 0, 2, 2, 1]))
else
(if i.val < 4246 then
[1, 1, 2, 1, 1, 0, 2, 3, 0, 0]
else
(if i.val < 4247 then
[1, 1, 2, 1, 1, 0, 2, 3, 0, 2]
else
[1, 1, 2, 1, 1, 0, 2, 3, 2, 1])))))
else
(if i.val < 4260 then
(if i.val < 4254 then
(if i.val < 4251 then
(if i.val < 4249 then
[1, 1, 2, 1, 1, 2, 3, 3, 0, 1]
else
(if i.val < 4250 then
[1, 1, 2, 2, 3, 0, 1, 2, 3, 3]
else
[1, 1, 2, 3, 0, 1, 1, 2, 1, 0]))
else
(if i.val < 4252 then
[1, 1, 2, 3, 0, 1, 1, 2, 1, 1]
else
(if i.val < 4253 then
[1, 1, 3, 0, 0, 1, 2, 3, 3, 2]
else
[1, 1, 3, 0, 2, 2, 1, 3, 3, 2])))
else
(if i.val < 4257 then
(if i.val < 4255 then
[1, 1, 3, 0, 2, 3, 3, 0, 2, 1]
else
(if i.val < 4256 then
[1, 1, 3, 2, 2, 1, 0, 3, 2, 1]
else
[1, 2, 1, 1, 0, 2, 3, 0, 2, 1]))
else
(if i.val < 4258 then
[1, 2, 1, 1, 3, 0, 1, 2, 2, 1]
else
(if i.val < 4259 then
[1, 2, 1, 3, 0, 0, 3, 2, 2, 1]
else
[1, 2, 1, 3, 0, 1, 2, 2, 1, 3]))))
else
(if i.val < 4266 then
(if i.val < 4263 then
(if i.val < 4261 then
[1, 2, 2, 1, 0, 3, 0, 2, 1, 0]
else
(if i.val < 4262 then
[1, 2, 2, 3, 0, 0, 1, 2, 2, 3]
else
[1, 2, 3, 0, 0, 3, 2, 2, 1, 3]))
else
(if i.val < 4264 then
[1, 2, 3, 0, 1, 1, 0, 3, 2, 1]
else
(if i.val < 4265 then
[1, 2, 3, 0, 1, 2, 2, 1, 3, 3]
else
[1, 2, 3, 2, 2, 1, 0, 3, 2, 2])))
else
(if i.val < 4269 then
(if i.val < 4267 then
[1, 2, 3, 3, 0, 1, 2, 1, 0, 0]
else
(if i.val < 4268 then
[1, 3, 0, 0, 2, 2, 3, 2, 2, 1]
else
[1, 3, 0, 1, 1, 0, 2, 1, 1, 2]))
else
(if i.val < 4270 then
[1, 3, 0, 2, 1, 1, 0, 0, 2, 1]
else
(if i.val < 4271 then
[1, 3, 0, 2, 1, 1, 0, 0, 2, 3]
else
[1, 3, 2, 1, 0, 0, 3, 2, 2, 1]))))))
else
(if i.val < 4296 then
(if i.val < 4284 then
(if i.val < 4278 then
(if i.val < 4275 then
(if i.val < 4273 then
[1, 3, 3, 0, 1, 2, 1, 1, 0, 2]
else
(if i.val < 4274 then
[1, 3, 3, 0, 2, 1, 1, 0, 2, 1]
else
[2, 1, 0, 3, 3, 0, 2, 3, 3, 2]))
else
(if i.val < 4276 then
[2, 1, 1, 0, 3, 2, 1, 1, 0, 0]
else
(if i.val < 4277 then
[2, 1, 1, 3, 0, 2, 3, 3, 2, 1]
else
[2, 2, 3, 2, 2, 1, 3, 0, 1, 2])))
else
(if i.val < 4281 then
(if i.val < 4279 then
[2, 3, 0, 1, 1, 0, 2, 1, 1, 2]
else
(if i.val < 4280 then
[2, 3, 0, 1, 1, 0, 3, 2, 1, 1]
else
[2, 3, 0, 2, 1, 1, 2, 3, 3, 0]))
else
(if i.val < 4282 then
[2, 3, 2, 1, 0, 0, 3, 2, 2, 1]
else
(if i.val < 4283 then
[2, 3, 3, 0, 0, 2, 1, 1, 2, 3]
else
[2, 3, 3, 0, 1, 2, 1, 3, 3, 0]))))
else
(if i.val < 4290 then
(if i.val < 4287 then
(if i.val < 4285 then
[3, 0, 0, 3, 2, 2, 3, 0, 1, 2]
else
(if i.val < 4286 then
[3, 0, 1, 1, 0, 3, 2, 1, 1, 2]
else
[3, 0, 1, 2, 1, 3, 3, 0, 1, 2]))
else
(if i.val < 4288 then
[3, 0, 1, 2, 2, 1, 3, 0, 1, 2]
else
(if i.val < 4289 then
[3, 2, 1, 0, 3, 2, 2, 1, 1, 3]
else
[3, 2, 1, 1, 0, 2, 3, 0, 2, 1])))
else
(if i.val < 4293 then
(if i.val < 4291 then
[3, 3, 0, 1, 1, 0, 2, 1, 1, 2]
else
(if i.val < 4292 then
[3, 3, 0, 1, 1, 0, 3, 2, 1, 1]
else
[3, 3, 0, 2, 3, 3, 2, 1, 0, 0]))
else
(if i.val < 4294 then
[0, 0, 1, 0, 0, 2, 1, 1, 2, 3, 0]
else
(if i.val < 4295 then
[0, 0, 1, 0, 2, 3, 0, 1, 1, 2, 3]
else
[0, 0, 1, 0, 2, 3, 3, 0, 1, 2, 1])))))
else
(if i.val < 4308 then
(if i.val < 4302 then
(if i.val < 4299 then
(if i.val < 4297 then
[0, 0, 1, 0, 3, 2, 2, 1, 0, 3, 2]
else
(if i.val < 4298 then
[0, 0, 1, 2, 3, 0, 1, 2, 2, 3, 0]
else
[0, 0, 2, 1, 1, 3, 0, 2, 3, 3, 2]))
else
(if i.val < 4300 then
[0, 0, 2, 1, 3, 3, 0, 2, 1, 1, 2]
else
(if i.val < 4301 then
[0, 0, 2, 2, 3, 2, 1, 0, 3, 2, 2]
else
[0, 0, 2, 3, 2, 2, 1, 3, 0, 1, 2])))
else
(if i.val < 4305 then
(if i.val < 4303 then
[0, 0, 3, 0, 0, 2, 2, 3, 2, 2, 1]
else
(if i.val < 4304 then
[0, 0, 3, 0, 1, 2, 1, 1, 0, 2, 3]
else
[0, 0, 3, 0, 1, 2, 3, 3, 2, 1, 1]))
else
(if i.val < 4306 then
[0, 0, 3, 2, 2, 3, 0, 1, 2, 3, 3]
else
(if i.val < 4307 then
[0, 1, 0, 2, 3, 0, 1, 1, 2, 1, 1]
else
[0, 1, 0, 2, 3, 3, 0, 1, 2, 1, 1]))))
else
(if i.val < 4314 then
(if i.val < 4311 then
(if i.val < 4309 then
[0, 1, 0, 2, 3, 3, 0, 1, 2, 1, 3]
else
(if i.val < 4310 then
[0, 1, 0, 3, 3, 2, 1, 0, 3, 2, 2]
else
[0, 1, 1, 0, 3, 2, 1, 1, 2, 3, 0]))
else
(if i.val < 4312 then
[0, 1, 1, 2, 1, 1, 2, 3, 3, 0, 1]
else
(if i.val < 4313 then
[0, 1, 1, 2, 3, 0, 1, 1, 2, 1, 0]
else
[0, 1, 1, 2, 3, 0, 1, 1, 2, 1, 1])))
else
(if i.val < 4317 then
(if i.val < 4315 then
[0, 1, 1, 3, 2, 2, 1, 0, 3, 2, 1]
else
(if i.val < 4316 then
[0, 1, 2, 1, 3, 0, 0, 3, 2, 2, 1]
else
[0, 1, 2, 3, 2, 2, 1, 0, 3, 2, 2]))
else
(if i.val < 4318 then
[0, 3, 3, 0, 2, 3, 3, 2, 1, 0, 0]
else
(if i.val < 4319 then
[1, 0, 2, 3, 3, 0, 1, 1, 0, 2, 3]
else
[2, 3, 0, 1, 1, 0, 3, 2, 1, 1, 2])))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row18_cosetRepresentatives : Fin 4320 → HurwitzPrymRex_Mat :=
  fun i => (if i.val < 2176 then
(if i.val < 1024 then
(if i.val < 512 then
(if i.val < 256 then
(if i.val < 128 then
g32p_row18_cosetRepresentativesPart0000 i
else
g32p_row18_cosetRepresentativesPart0001 i)
else
(if i.val < 384 then
g32p_row18_cosetRepresentativesPart0002 i
else
g32p_row18_cosetRepresentativesPart0003 i))
else
(if i.val < 768 then
(if i.val < 640 then
g32p_row18_cosetRepresentativesPart0004 i
else
g32p_row18_cosetRepresentativesPart0005 i)
else
(if i.val < 896 then
g32p_row18_cosetRepresentativesPart0006 i
else
g32p_row18_cosetRepresentativesPart0007 i)))
else
(if i.val < 1536 then
(if i.val < 1280 then
(if i.val < 1152 then
g32p_row18_cosetRepresentativesPart0008 i
else
g32p_row18_cosetRepresentativesPart0009 i)
else
(if i.val < 1408 then
g32p_row18_cosetRepresentativesPart0010 i
else
g32p_row18_cosetRepresentativesPart0011 i))
else
(if i.val < 1792 then
(if i.val < 1664 then
g32p_row18_cosetRepresentativesPart0012 i
else
g32p_row18_cosetRepresentativesPart0013 i)
else
(if i.val < 1920 then
g32p_row18_cosetRepresentativesPart0014 i
else
(if i.val < 2048 then
g32p_row18_cosetRepresentativesPart0015 i
else
g32p_row18_cosetRepresentativesPart0016 i)))))
else
(if i.val < 3200 then
(if i.val < 2688 then
(if i.val < 2432 then
(if i.val < 2304 then
g32p_row18_cosetRepresentativesPart0017 i
else
g32p_row18_cosetRepresentativesPart0018 i)
else
(if i.val < 2560 then
g32p_row18_cosetRepresentativesPart0019 i
else
g32p_row18_cosetRepresentativesPart0020 i))
else
(if i.val < 2944 then
(if i.val < 2816 then
g32p_row18_cosetRepresentativesPart0021 i
else
g32p_row18_cosetRepresentativesPart0022 i)
else
(if i.val < 3072 then
g32p_row18_cosetRepresentativesPart0023 i
else
g32p_row18_cosetRepresentativesPart0024 i)))
else
(if i.val < 3712 then
(if i.val < 3456 then
(if i.val < 3328 then
g32p_row18_cosetRepresentativesPart0025 i
else
g32p_row18_cosetRepresentativesPart0026 i)
else
(if i.val < 3584 then
g32p_row18_cosetRepresentativesPart0027 i
else
g32p_row18_cosetRepresentativesPart0028 i))
else
(if i.val < 3968 then
(if i.val < 3840 then
g32p_row18_cosetRepresentativesPart0029 i
else
g32p_row18_cosetRepresentativesPart0030 i)
else
(if i.val < 4096 then
g32p_row18_cosetRepresentativesPart0031 i
else
(if i.val < 4224 then
g32p_row18_cosetRepresentativesPart0032 i
else
g32p_row18_cosetRepresentativesPart0033 i))))))

def g32p_row18_cosetWords : Fin 4320 → List (Fin 4) :=
  fun i => (if i.val < 2176 then
(if i.val < 1024 then
(if i.val < 512 then
(if i.val < 256 then
(if i.val < 128 then
g32p_row18_cosetWordsPart0000 i
else
g32p_row18_cosetWordsPart0001 i)
else
(if i.val < 384 then
g32p_row18_cosetWordsPart0002 i
else
g32p_row18_cosetWordsPart0003 i))
else
(if i.val < 768 then
(if i.val < 640 then
g32p_row18_cosetWordsPart0004 i
else
g32p_row18_cosetWordsPart0005 i)
else
(if i.val < 896 then
g32p_row18_cosetWordsPart0006 i
else
g32p_row18_cosetWordsPart0007 i)))
else
(if i.val < 1536 then
(if i.val < 1280 then
(if i.val < 1152 then
g32p_row18_cosetWordsPart0008 i
else
g32p_row18_cosetWordsPart0009 i)
else
(if i.val < 1408 then
g32p_row18_cosetWordsPart0010 i
else
g32p_row18_cosetWordsPart0011 i))
else
(if i.val < 1792 then
(if i.val < 1664 then
g32p_row18_cosetWordsPart0012 i
else
g32p_row18_cosetWordsPart0013 i)
else
(if i.val < 1920 then
g32p_row18_cosetWordsPart0014 i
else
(if i.val < 2048 then
g32p_row18_cosetWordsPart0015 i
else
g32p_row18_cosetWordsPart0016 i)))))
else
(if i.val < 3200 then
(if i.val < 2688 then
(if i.val < 2432 then
(if i.val < 2304 then
g32p_row18_cosetWordsPart0017 i
else
g32p_row18_cosetWordsPart0018 i)
else
(if i.val < 2560 then
g32p_row18_cosetWordsPart0019 i
else
g32p_row18_cosetWordsPart0020 i))
else
(if i.val < 2944 then
(if i.val < 2816 then
g32p_row18_cosetWordsPart0021 i
else
g32p_row18_cosetWordsPart0022 i)
else
(if i.val < 3072 then
g32p_row18_cosetWordsPart0023 i
else
g32p_row18_cosetWordsPart0024 i)))
else
(if i.val < 3712 then
(if i.val < 3456 then
(if i.val < 3328 then
g32p_row18_cosetWordsPart0025 i
else
g32p_row18_cosetWordsPart0026 i)
else
(if i.val < 3584 then
g32p_row18_cosetWordsPart0027 i
else
g32p_row18_cosetWordsPart0028 i))
else
(if i.val < 3968 then
(if i.val < 3840 then
g32p_row18_cosetWordsPart0029 i
else
g32p_row18_cosetWordsPart0030 i)
else
(if i.val < 4096 then
g32p_row18_cosetWordsPart0031 i
else
(if i.val < 4224 then
g32p_row18_cosetWordsPart0032 i
else
g32p_row18_cosetWordsPart0033 i))))))

def g32p_row18_cosetBranchMatrices : Fin 3 → HurwitzPrymRex_Mat :=
  ![![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]], ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, -2⟩, ⟨0, -2⟩, ⟨-1, -2⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩]], ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩]]]

def g32p_row18_cosetGeneratorNextColumn0 : Fin 4320 → Fin 4320 :=
  fun i => (if i.val < 2048 then
(if i.val < 1024 then
(if i.val < 512 then
g32p_row18_cosetGeneratorNextColumn0Part0000 i
else
g32p_row18_cosetGeneratorNextColumn0Part0001 i)
else
(if i.val < 1536 then
g32p_row18_cosetGeneratorNextColumn0Part0002 i
else
g32p_row18_cosetGeneratorNextColumn0Part0003 i))
else
(if i.val < 3072 then
(if i.val < 2560 then
g32p_row18_cosetGeneratorNextColumn0Part0004 i
else
g32p_row18_cosetGeneratorNextColumn0Part0005 i)
else
(if i.val < 3584 then
g32p_row18_cosetGeneratorNextColumn0Part0006 i
else
(if i.val < 4096 then
g32p_row18_cosetGeneratorNextColumn0Part0007 i
else
g32p_row18_cosetGeneratorNextColumn0Part0008 i))))

def g32p_row18_cosetGeneratorNextColumn1 : Fin 4320 → Fin 4320 :=
  fun i => (if i.val < 2048 then
(if i.val < 1024 then
(if i.val < 512 then
g32p_row18_cosetGeneratorNextColumn1Part0000 i
else
g32p_row18_cosetGeneratorNextColumn1Part0001 i)
else
(if i.val < 1536 then
g32p_row18_cosetGeneratorNextColumn1Part0002 i
else
g32p_row18_cosetGeneratorNextColumn1Part0003 i))
else
(if i.val < 3072 then
(if i.val < 2560 then
g32p_row18_cosetGeneratorNextColumn1Part0004 i
else
g32p_row18_cosetGeneratorNextColumn1Part0005 i)
else
(if i.val < 3584 then
g32p_row18_cosetGeneratorNextColumn1Part0006 i
else
(if i.val < 4096 then
g32p_row18_cosetGeneratorNextColumn1Part0007 i
else
g32p_row18_cosetGeneratorNextColumn1Part0008 i))))

def g32p_row18_cosetGeneratorNextColumn2 : Fin 4320 → Fin 4320 :=
  fun i => (if i.val < 2048 then
(if i.val < 1024 then
(if i.val < 512 then
g32p_row18_cosetGeneratorNextColumn2Part0000 i
else
g32p_row18_cosetGeneratorNextColumn2Part0001 i)
else
(if i.val < 1536 then
g32p_row18_cosetGeneratorNextColumn2Part0002 i
else
g32p_row18_cosetGeneratorNextColumn2Part0003 i))
else
(if i.val < 3072 then
(if i.val < 2560 then
g32p_row18_cosetGeneratorNextColumn2Part0004 i
else
g32p_row18_cosetGeneratorNextColumn2Part0005 i)
else
(if i.val < 3584 then
g32p_row18_cosetGeneratorNextColumn2Part0006 i
else
(if i.val < 4096 then
g32p_row18_cosetGeneratorNextColumn2Part0007 i
else
g32p_row18_cosetGeneratorNextColumn2Part0008 i))))

def g32p_row18_cosetGeneratorNextColumn3 : Fin 4320 → Fin 4320 :=
  fun i => (if i.val < 2048 then
(if i.val < 1024 then
(if i.val < 512 then
g32p_row18_cosetGeneratorNextColumn3Part0000 i
else
g32p_row18_cosetGeneratorNextColumn3Part0001 i)
else
(if i.val < 1536 then
g32p_row18_cosetGeneratorNextColumn3Part0002 i
else
g32p_row18_cosetGeneratorNextColumn3Part0003 i))
else
(if i.val < 3072 then
(if i.val < 2560 then
g32p_row18_cosetGeneratorNextColumn3Part0004 i
else
g32p_row18_cosetGeneratorNextColumn3Part0005 i)
else
(if i.val < 3584 then
g32p_row18_cosetGeneratorNextColumn3Part0006 i
else
(if i.val < 4096 then
g32p_row18_cosetGeneratorNextColumn3Part0007 i
else
g32p_row18_cosetGeneratorNextColumn3Part0008 i))))

def g32p_row18_cosetGeneratorNext : Fin 4 → Fin 4320 → Fin 4320 :=
  ![g32p_row18_cosetGeneratorNextColumn0, g32p_row18_cosetGeneratorNextColumn1, g32p_row18_cosetGeneratorNextColumn2, g32p_row18_cosetGeneratorNextColumn3]

def g32p_row18_cosetGeneratorFactorColumn0 : Fin 4320 → Fin 36 :=
  fun i => (if i.val < 2048 then
(if i.val < 1024 then
(if i.val < 512 then
g32p_row18_cosetGeneratorFactorColumn0Part0000 i
else
g32p_row18_cosetGeneratorFactorColumn0Part0001 i)
else
(if i.val < 1536 then
g32p_row18_cosetGeneratorFactorColumn0Part0002 i
else
g32p_row18_cosetGeneratorFactorColumn0Part0003 i))
else
(if i.val < 3072 then
(if i.val < 2560 then
g32p_row18_cosetGeneratorFactorColumn0Part0004 i
else
g32p_row18_cosetGeneratorFactorColumn0Part0005 i)
else
(if i.val < 3584 then
g32p_row18_cosetGeneratorFactorColumn0Part0006 i
else
(if i.val < 4096 then
g32p_row18_cosetGeneratorFactorColumn0Part0007 i
else
g32p_row18_cosetGeneratorFactorColumn0Part0008 i))))

def g32p_row18_cosetGeneratorFactorColumn1 : Fin 4320 → Fin 36 :=
  fun i => (if i.val < 2048 then
(if i.val < 1024 then
(if i.val < 512 then
g32p_row18_cosetGeneratorFactorColumn1Part0000 i
else
g32p_row18_cosetGeneratorFactorColumn1Part0001 i)
else
(if i.val < 1536 then
g32p_row18_cosetGeneratorFactorColumn1Part0002 i
else
g32p_row18_cosetGeneratorFactorColumn1Part0003 i))
else
(if i.val < 3072 then
(if i.val < 2560 then
g32p_row18_cosetGeneratorFactorColumn1Part0004 i
else
g32p_row18_cosetGeneratorFactorColumn1Part0005 i)
else
(if i.val < 3584 then
g32p_row18_cosetGeneratorFactorColumn1Part0006 i
else
(if i.val < 4096 then
g32p_row18_cosetGeneratorFactorColumn1Part0007 i
else
g32p_row18_cosetGeneratorFactorColumn1Part0008 i))))

def g32p_row18_cosetGeneratorFactorColumn2 : Fin 4320 → Fin 36 :=
  fun i => (if i.val < 2048 then
(if i.val < 1024 then
(if i.val < 512 then
g32p_row18_cosetGeneratorFactorColumn2Part0000 i
else
g32p_row18_cosetGeneratorFactorColumn2Part0001 i)
else
(if i.val < 1536 then
g32p_row18_cosetGeneratorFactorColumn2Part0002 i
else
g32p_row18_cosetGeneratorFactorColumn2Part0003 i))
else
(if i.val < 3072 then
(if i.val < 2560 then
g32p_row18_cosetGeneratorFactorColumn2Part0004 i
else
g32p_row18_cosetGeneratorFactorColumn2Part0005 i)
else
(if i.val < 3584 then
g32p_row18_cosetGeneratorFactorColumn2Part0006 i
else
(if i.val < 4096 then
g32p_row18_cosetGeneratorFactorColumn2Part0007 i
else
g32p_row18_cosetGeneratorFactorColumn2Part0008 i))))

def g32p_row18_cosetGeneratorFactorColumn3 : Fin 4320 → Fin 36 :=
  fun i => (if i.val < 2048 then
(if i.val < 1024 then
(if i.val < 512 then
g32p_row18_cosetGeneratorFactorColumn3Part0000 i
else
g32p_row18_cosetGeneratorFactorColumn3Part0001 i)
else
(if i.val < 1536 then
g32p_row18_cosetGeneratorFactorColumn3Part0002 i
else
g32p_row18_cosetGeneratorFactorColumn3Part0003 i))
else
(if i.val < 3072 then
(if i.val < 2560 then
g32p_row18_cosetGeneratorFactorColumn3Part0004 i
else
g32p_row18_cosetGeneratorFactorColumn3Part0005 i)
else
(if i.val < 3584 then
g32p_row18_cosetGeneratorFactorColumn3Part0006 i
else
(if i.val < 4096 then
g32p_row18_cosetGeneratorFactorColumn3Part0007 i
else
g32p_row18_cosetGeneratorFactorColumn3Part0008 i))))

def g32p_row18_cosetGeneratorFactor : Fin 4 → Fin 4320 → Fin 36 :=
  ![g32p_row18_cosetGeneratorFactorColumn0, g32p_row18_cosetGeneratorFactorColumn1, g32p_row18_cosetGeneratorFactorColumn2, g32p_row18_cosetGeneratorFactorColumn3]

def g32p_row18_cosetBranchNextColumn0 : Fin 4320 → Fin 4320 :=
  fun i => (if i.val < 2048 then
(if i.val < 1024 then
(if i.val < 512 then
g32p_row18_cosetBranchNextColumn0Part0000 i
else
g32p_row18_cosetBranchNextColumn0Part0001 i)
else
(if i.val < 1536 then
g32p_row18_cosetBranchNextColumn0Part0002 i
else
g32p_row18_cosetBranchNextColumn0Part0003 i))
else
(if i.val < 3072 then
(if i.val < 2560 then
g32p_row18_cosetBranchNextColumn0Part0004 i
else
g32p_row18_cosetBranchNextColumn0Part0005 i)
else
(if i.val < 3584 then
g32p_row18_cosetBranchNextColumn0Part0006 i
else
(if i.val < 4096 then
g32p_row18_cosetBranchNextColumn0Part0007 i
else
g32p_row18_cosetBranchNextColumn0Part0008 i))))

def g32p_row18_cosetBranchNextColumn1 : Fin 4320 → Fin 4320 :=
  fun i => (if i.val < 2048 then
(if i.val < 1024 then
(if i.val < 512 then
g32p_row18_cosetBranchNextColumn1Part0000 i
else
g32p_row18_cosetBranchNextColumn1Part0001 i)
else
(if i.val < 1536 then
g32p_row18_cosetBranchNextColumn1Part0002 i
else
g32p_row18_cosetBranchNextColumn1Part0003 i))
else
(if i.val < 3072 then
(if i.val < 2560 then
g32p_row18_cosetBranchNextColumn1Part0004 i
else
g32p_row18_cosetBranchNextColumn1Part0005 i)
else
(if i.val < 3584 then
g32p_row18_cosetBranchNextColumn1Part0006 i
else
(if i.val < 4096 then
g32p_row18_cosetBranchNextColumn1Part0007 i
else
g32p_row18_cosetBranchNextColumn1Part0008 i))))

def g32p_row18_cosetBranchNextColumn2 : Fin 4320 → Fin 4320 :=
  fun i => (if i.val < 2048 then
(if i.val < 1024 then
(if i.val < 512 then
g32p_row18_cosetBranchNextColumn2Part0000 i
else
g32p_row18_cosetBranchNextColumn2Part0001 i)
else
(if i.val < 1536 then
g32p_row18_cosetBranchNextColumn2Part0002 i
else
g32p_row18_cosetBranchNextColumn2Part0003 i))
else
(if i.val < 3072 then
(if i.val < 2560 then
g32p_row18_cosetBranchNextColumn2Part0004 i
else
g32p_row18_cosetBranchNextColumn2Part0005 i)
else
(if i.val < 3584 then
g32p_row18_cosetBranchNextColumn2Part0006 i
else
(if i.val < 4096 then
g32p_row18_cosetBranchNextColumn2Part0007 i
else
g32p_row18_cosetBranchNextColumn2Part0008 i))))

def g32p_row18_cosetBranchNext : Fin 3 → Fin 4320 → Fin 4320 :=
  ![g32p_row18_cosetBranchNextColumn0, g32p_row18_cosetBranchNextColumn1, g32p_row18_cosetBranchNextColumn2]

def g32p_row18_cosetBranchFactorColumn0 : Fin 4320 → Fin 36 :=
  fun i => (if i.val < 2048 then
(if i.val < 1024 then
(if i.val < 512 then
g32p_row18_cosetBranchFactorColumn0Part0000 i
else
g32p_row18_cosetBranchFactorColumn0Part0001 i)
else
(if i.val < 1536 then
g32p_row18_cosetBranchFactorColumn0Part0002 i
else
g32p_row18_cosetBranchFactorColumn0Part0003 i))
else
(if i.val < 3072 then
(if i.val < 2560 then
g32p_row18_cosetBranchFactorColumn0Part0004 i
else
g32p_row18_cosetBranchFactorColumn0Part0005 i)
else
(if i.val < 3584 then
g32p_row18_cosetBranchFactorColumn0Part0006 i
else
(if i.val < 4096 then
g32p_row18_cosetBranchFactorColumn0Part0007 i
else
g32p_row18_cosetBranchFactorColumn0Part0008 i))))

def g32p_row18_cosetBranchFactorColumn1 : Fin 4320 → Fin 36 :=
  fun i => (if i.val < 2048 then
(if i.val < 1024 then
(if i.val < 512 then
g32p_row18_cosetBranchFactorColumn1Part0000 i
else
g32p_row18_cosetBranchFactorColumn1Part0001 i)
else
(if i.val < 1536 then
g32p_row18_cosetBranchFactorColumn1Part0002 i
else
g32p_row18_cosetBranchFactorColumn1Part0003 i))
else
(if i.val < 3072 then
(if i.val < 2560 then
g32p_row18_cosetBranchFactorColumn1Part0004 i
else
g32p_row18_cosetBranchFactorColumn1Part0005 i)
else
(if i.val < 3584 then
g32p_row18_cosetBranchFactorColumn1Part0006 i
else
(if i.val < 4096 then
g32p_row18_cosetBranchFactorColumn1Part0007 i
else
g32p_row18_cosetBranchFactorColumn1Part0008 i))))

def g32p_row18_cosetBranchFactorColumn2 : Fin 4320 → Fin 36 :=
  fun i => (if i.val < 2048 then
(if i.val < 1024 then
(if i.val < 512 then
g32p_row18_cosetBranchFactorColumn2Part0000 i
else
g32p_row18_cosetBranchFactorColumn2Part0001 i)
else
(if i.val < 1536 then
g32p_row18_cosetBranchFactorColumn2Part0002 i
else
g32p_row18_cosetBranchFactorColumn2Part0003 i))
else
(if i.val < 3072 then
(if i.val < 2560 then
g32p_row18_cosetBranchFactorColumn2Part0004 i
else
g32p_row18_cosetBranchFactorColumn2Part0005 i)
else
(if i.val < 3584 then
g32p_row18_cosetBranchFactorColumn2Part0006 i
else
(if i.val < 4096 then
g32p_row18_cosetBranchFactorColumn2Part0007 i
else
g32p_row18_cosetBranchFactorColumn2Part0008 i))))

def g32p_row18_cosetBranchFactor : Fin 3 → Fin 4320 → Fin 36 :=
  ![g32p_row18_cosetBranchFactorColumn0, g32p_row18_cosetBranchFactorColumn1, g32p_row18_cosetBranchFactorColumn2]

def g32p_row18_cosetLabels0 : Fin 4320 → Fin 1440 :=
  fun i => (if i.val < 2048 then
(if i.val < 1024 then
(if i.val < 512 then
g32p_row18_cosetLabels0Part0000 i
else
g32p_row18_cosetLabels0Part0001 i)
else
(if i.val < 1536 then
g32p_row18_cosetLabels0Part0002 i
else
g32p_row18_cosetLabels0Part0003 i))
else
(if i.val < 3072 then
(if i.val < 2560 then
g32p_row18_cosetLabels0Part0004 i
else
g32p_row18_cosetLabels0Part0005 i)
else
(if i.val < 3584 then
g32p_row18_cosetLabels0Part0006 i
else
(if i.val < 4096 then
g32p_row18_cosetLabels0Part0007 i
else
g32p_row18_cosetLabels0Part0008 i))))

def g32p_row18_cosetDistances0 : Fin 4320 → ℕ :=
  fun i => (if i.val < 2048 then
(if i.val < 1024 then
(if i.val < 512 then
g32p_row18_cosetDistances0Part0000 i
else
g32p_row18_cosetDistances0Part0001 i)
else
(if i.val < 1536 then
g32p_row18_cosetDistances0Part0002 i
else
g32p_row18_cosetDistances0Part0003 i))
else
(if i.val < 3072 then
(if i.val < 2560 then
g32p_row18_cosetDistances0Part0004 i
else
g32p_row18_cosetDistances0Part0005 i)
else
(if i.val < 3584 then
g32p_row18_cosetDistances0Part0006 i
else
(if i.val < 4096 then
g32p_row18_cosetDistances0Part0007 i
else
g32p_row18_cosetDistances0Part0008 i))))

def g32p_row18_cosetRoots0 : Fin 1440 → Fin 4320 :=
  fun i => (if i.val < 512 then
g32p_row18_cosetRoots0Part0000 i
else
(if i.val < 1024 then
g32p_row18_cosetRoots0Part0001 i
else
g32p_row18_cosetRoots0Part0002 i))

def g32p_row18_cosetLengths0 : Fin 1440 → ℕ :=
  fun i => (if i.val < 512 then
g32p_row18_cosetLengths0Part0000 i
else
(if i.val < 1024 then
g32p_row18_cosetLengths0Part0001 i
else
g32p_row18_cosetLengths0Part0002 i))

def g32p_row18_cosetCycleNodes0 : Fin 1440 → List ℕ :=
  fun i => (if i.val < 512 then
g32p_row18_cosetCycleNodes0Part0000 i
else
(if i.val < 1024 then
g32p_row18_cosetCycleNodes0Part0001 i
else
g32p_row18_cosetCycleNodes0Part0002 i))

def g32p_row18_cosetCycles0 : List (List ℕ) :=
  List.ofFn g32p_row18_cosetCycleNodes0

def g32p_row18_cosetMonodromies0 : Fin 1440 → Fin 36 :=
  fun i => (if i.val < 512 then
g32p_row18_cosetMonodromies0Part0000 i
else
(if i.val < 1024 then
g32p_row18_cosetMonodromies0Part0001 i
else
g32p_row18_cosetMonodromies0Part0002 i))

def g32p_row18_cosetExponents0 : Fin 1440 → Multiplicative (ZMod 6) :=
  fun i => (if i.val < 512 then
g32p_row18_cosetExponents0Part0000 i
else
(if i.val < 1024 then
g32p_row18_cosetExponents0Part0001 i
else
g32p_row18_cosetExponents0Part0002 i))

def g32p_row18_cosetLabels1 : Fin 4320 → Fin 1440 :=
  fun i => (if i.val < 2048 then
(if i.val < 1024 then
(if i.val < 512 then
g32p_row18_cosetLabels1Part0000 i
else
g32p_row18_cosetLabels1Part0001 i)
else
(if i.val < 1536 then
g32p_row18_cosetLabels1Part0002 i
else
g32p_row18_cosetLabels1Part0003 i))
else
(if i.val < 3072 then
(if i.val < 2560 then
g32p_row18_cosetLabels1Part0004 i
else
g32p_row18_cosetLabels1Part0005 i)
else
(if i.val < 3584 then
g32p_row18_cosetLabels1Part0006 i
else
(if i.val < 4096 then
g32p_row18_cosetLabels1Part0007 i
else
g32p_row18_cosetLabels1Part0008 i))))

def g32p_row18_cosetDistances1 : Fin 4320 → ℕ :=
  fun i => (if i.val < 2048 then
(if i.val < 1024 then
(if i.val < 512 then
g32p_row18_cosetDistances1Part0000 i
else
g32p_row18_cosetDistances1Part0001 i)
else
(if i.val < 1536 then
g32p_row18_cosetDistances1Part0002 i
else
g32p_row18_cosetDistances1Part0003 i))
else
(if i.val < 3072 then
(if i.val < 2560 then
g32p_row18_cosetDistances1Part0004 i
else
g32p_row18_cosetDistances1Part0005 i)
else
(if i.val < 3584 then
g32p_row18_cosetDistances1Part0006 i
else
(if i.val < 4096 then
g32p_row18_cosetDistances1Part0007 i
else
g32p_row18_cosetDistances1Part0008 i))))

def g32p_row18_cosetRoots1 : Fin 1440 → Fin 4320 :=
  fun i => (if i.val < 512 then
g32p_row18_cosetRoots1Part0000 i
else
(if i.val < 1024 then
g32p_row18_cosetRoots1Part0001 i
else
g32p_row18_cosetRoots1Part0002 i))

def g32p_row18_cosetLengths1 : Fin 1440 → ℕ :=
  fun i => (if i.val < 512 then
g32p_row18_cosetLengths1Part0000 i
else
(if i.val < 1024 then
g32p_row18_cosetLengths1Part0001 i
else
g32p_row18_cosetLengths1Part0002 i))

def g32p_row18_cosetCycleNodes1 : Fin 1440 → List ℕ :=
  fun i => (if i.val < 512 then
g32p_row18_cosetCycleNodes1Part0000 i
else
(if i.val < 1024 then
g32p_row18_cosetCycleNodes1Part0001 i
else
g32p_row18_cosetCycleNodes1Part0002 i))

def g32p_row18_cosetCycles1 : List (List ℕ) :=
  List.ofFn g32p_row18_cosetCycleNodes1

def g32p_row18_cosetMonodromies1 : Fin 1440 → Fin 36 :=
  fun i => (if i.val < 512 then
g32p_row18_cosetMonodromies1Part0000 i
else
(if i.val < 1024 then
g32p_row18_cosetMonodromies1Part0001 i
else
g32p_row18_cosetMonodromies1Part0002 i))

def g32p_row18_cosetExponents1 : Fin 1440 → Multiplicative (ZMod 6) :=
  fun i => (if i.val < 512 then
g32p_row18_cosetExponents1Part0000 i
else
(if i.val < 1024 then
g32p_row18_cosetExponents1Part0001 i
else
g32p_row18_cosetExponents1Part0002 i))

def g32p_row18_cosetLabels2 : Fin 4320 → Fin 2208 :=
  fun i => (if i.val < 2048 then
(if i.val < 1024 then
(if i.val < 512 then
g32p_row18_cosetLabels2Part0000 i
else
g32p_row18_cosetLabels2Part0001 i)
else
(if i.val < 1536 then
g32p_row18_cosetLabels2Part0002 i
else
g32p_row18_cosetLabels2Part0003 i))
else
(if i.val < 3072 then
(if i.val < 2560 then
g32p_row18_cosetLabels2Part0004 i
else
g32p_row18_cosetLabels2Part0005 i)
else
(if i.val < 3584 then
g32p_row18_cosetLabels2Part0006 i
else
(if i.val < 4096 then
g32p_row18_cosetLabels2Part0007 i
else
g32p_row18_cosetLabels2Part0008 i))))

def g32p_row18_cosetDistances2 : Fin 4320 → ℕ :=
  fun i => (if i.val < 2048 then
(if i.val < 1024 then
(if i.val < 512 then
g32p_row18_cosetDistances2Part0000 i
else
g32p_row18_cosetDistances2Part0001 i)
else
(if i.val < 1536 then
g32p_row18_cosetDistances2Part0002 i
else
g32p_row18_cosetDistances2Part0003 i))
else
(if i.val < 3072 then
(if i.val < 2560 then
g32p_row18_cosetDistances2Part0004 i
else
g32p_row18_cosetDistances2Part0005 i)
else
(if i.val < 3584 then
g32p_row18_cosetDistances2Part0006 i
else
(if i.val < 4096 then
g32p_row18_cosetDistances2Part0007 i
else
g32p_row18_cosetDistances2Part0008 i))))

def g32p_row18_cosetRoots2 : Fin 2208 → Fin 4320 :=
  fun i => (if i.val < 1024 then
(if i.val < 512 then
g32p_row18_cosetRoots2Part0000 i
else
g32p_row18_cosetRoots2Part0001 i)
else
(if i.val < 1536 then
g32p_row18_cosetRoots2Part0002 i
else
(if i.val < 2048 then
g32p_row18_cosetRoots2Part0003 i
else
g32p_row18_cosetRoots2Part0004 i)))

def g32p_row18_cosetLengths2 : Fin 2208 → ℕ :=
  fun i => (if i.val < 1024 then
(if i.val < 512 then
g32p_row18_cosetLengths2Part0000 i
else
g32p_row18_cosetLengths2Part0001 i)
else
(if i.val < 1536 then
g32p_row18_cosetLengths2Part0002 i
else
(if i.val < 2048 then
g32p_row18_cosetLengths2Part0003 i
else
g32p_row18_cosetLengths2Part0004 i)))

def g32p_row18_cosetCycleNodes2 : Fin 2208 → List ℕ :=
  fun i => (if i.val < 1024 then
(if i.val < 512 then
g32p_row18_cosetCycleNodes2Part0000 i
else
g32p_row18_cosetCycleNodes2Part0001 i)
else
(if i.val < 1536 then
g32p_row18_cosetCycleNodes2Part0002 i
else
(if i.val < 2048 then
g32p_row18_cosetCycleNodes2Part0003 i
else
g32p_row18_cosetCycleNodes2Part0004 i)))

def g32p_row18_cosetCycles2 : List (List ℕ) :=
  List.ofFn g32p_row18_cosetCycleNodes2

def g32p_row18_cosetMonodromies2 : Fin 2208 → Fin 36 :=
  fun i => (if i.val < 1024 then
(if i.val < 512 then
g32p_row18_cosetMonodromies2Part0000 i
else
g32p_row18_cosetMonodromies2Part0001 i)
else
(if i.val < 1536 then
g32p_row18_cosetMonodromies2Part0002 i
else
(if i.val < 2048 then
g32p_row18_cosetMonodromies2Part0003 i
else
g32p_row18_cosetMonodromies2Part0004 i)))

def g32p_row18_cosetExponents2 : Fin 2208 → Multiplicative (ZMod 6) :=
  fun i => (if i.val < 1024 then
(if i.val < 512 then
g32p_row18_cosetExponents2Part0000 i
else
g32p_row18_cosetExponents2Part0001 i)
else
(if i.val < 1536 then
g32p_row18_cosetExponents2Part0002 i
else
(if i.val < 2048 then
g32p_row18_cosetExponents2Part0003 i
else
g32p_row18_cosetExponents2Part0004 i)))


end HodgeLean.Foundations.Program

end
