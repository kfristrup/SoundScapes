; modeling noise effects on wildlife. Created by Ben Pauli (Saint Mary's University of Minnesota), Chris McClure, Jesse Barber
; Cory Toth led the publication
; Kurt Fristrup (Colorado State University) revised the sound propagation and noise source code
;; introduced vehicles with calibrated source spectra and driver behavior (congestion)
;; converted to 1/3rd octave bands, ISO-9613 procedures
;; pressure squared calculations for spectral propagation until the terminal step for speed
;; lookup tables avoid ISO-9613 computations during ticks loop
;;;; for A-weighted calculations, ISO-9613 and spectral calculations used to create the distance-speed lookup table
;;;; spectral code conserved for future d-prime audibility calculations
; PENDING UPGRADES
; aggregate vehicle noise sources at high traffic densities to accelerate computation
;; group either by segments of road or clusters of vehicles, add noise together, and compute attenuation for an appropriate "average" path
; add options for intermittent audible cues for resources and searchers
;; would affect movements when resources are visited: course reversals would be possible
;; possible emergent interactions with timescales of noise events and searcher transit times
; use d-prime to determine audibility for wildlilfe and humans
; behavioral interactions among vehicles (drivers) and wildlife
;; recode to allow x-axis to have min-pxcor = ( - max-pxcor ) for crossing/collision simulations
; could introduce new agents as "hikers", and investigate wildlife-hiker interactions mediated by sound
; OPTION: might have used the LevelSpace extension to create the road (?execution speed?)
; Fristrup sought to use NetLogo hyphenated idiom, but some camel case and other names persist in the code

breed [ vehicles vehicle ]
breed [ searchers searcher ]
breed [ stations station ]

globals [
  ;SCALARS
  temp-test ; utility global for debugging
  ref-distance ; nominal distance for incoming NMSim sources (new sources must match!)
  meters-per-unitNL ; distance between patch centers in the ecological world
  num-ranges ; controls the density of the sound attenuation and range-speed lookup matrices
  speed-max ; used for range-spd-p2 and
  accel-jitter acc-jitt2 ; constants controlling small random fluctuations in acceleration, typically a few percent
  veh-per-hour vph-unblocked ; vehicles per hour (actual and if no congenstion)
  temp-kelvin base-searcher-size speed-min ; speed-min a small nonzero constant (logarithms)
  ambient-levelP2 ; all internal calculations are in pressure squared units
  base-percept-patches sspeed-patches ; converting from meters to NetLogo units
  kolr-decay ; controls the exponential decay of birder accessibility color on the trail
  base-birdable base-visited-rate ; estimates of encounter rates without noise
  sum-birdable sum-visited ; sum of ticks and resources across all searchers
  base-vehicles-hour num-resources ; traffic if no congestion; resource density affects movement and reduces search area!
  noise-decorrelate-ticks reflect-bias ; sound sampling interval for searchers; boundary aversion parameter
  mid-pxcor ; midpoint of world width, stored to economize calculations
  src-pow ; scalar -- median of the item 1 src-coefs
  ;LISTS WITH 24 VALUES, SPECTRAL COEFFICIENTS
  freqs aWt ambi-spectrum atten-absorp ; 1/3rd OB center frequencies, ambient, atmospheric absorption
  range-points ; list of distances for the attenuation and range-speed tables
  d-range-points ; diff range-points (expedites calculations)
  speed-points ; list of speeds for the range-speed table
  d-speed-points ; diff speed-points (expedites calculations)
  ;LISTS OF LISTS
  src-coefs ; list 2 of list 24 values: 1/3rd OB levels predicted by power law fits
  total-atten ; list 24 of length range-points: 1/3rd OB attenuation v range
  range-spd-p2 ; list of num-ranges of lists of num-speeds
]

vehicles-own [ ; vehicles before patches: potential noise-sensitive resources
  speed ; m/s
  speed-pps ; patches per second
  vspeed-limit ; m/s
]
patches-own [ ; landscape variables
  hab ; habitat type - matrix, resource, trail, or road
  quality ; quality of resource (1-100): not used for resource visitation or settlement at present
  ; times-visited: now tracked by searchers as an agentset
]
searchers-own [ ; searcher variables
  moving-to ; resource searcher is moving towards
  heard-not-visited ; candidates for moving-to
  resources-visited ; resources seen by the searcher
  resources-nonoise ; resources detected if no noise
  percept ;listening window for searcher in masked patches
  sound ; sound level in P^2
  sound-history ; list, noise exposures
  resourceNoise ; list, sound level when resource detected
  birderNoise ; list, birded noise, one per session
  birdable-lasttick ; last time searcher was birdable
  birdable-durations ; list, lengths of each session
  birdable-absences ; list, lengths of gaps
  birderX ; list, birded distance from road
  birdable-lasttickNN
  birdable-durationsNN
  birdable-absencesNN
  ; count of birded if no noise
]
stations-own [ ; station variables
  sound ; sound level in P^2
  sound-history ; list, noise exposures
  percept ; listening window for searcher in masked patches
  searchers-detected
  searchers-detectedNN
  sum-absent-noise ; for average level when no searchers detected
  absent-tick ; scalar, when last searcher departed
  absent-tickNN
  searchers-active ; ordered list: searchers in range
  searchers-firstick ; ordered list: last time searcher was detected
  searchers-activeNN ; ordered list: searches in range
  searchers-firstickNN ; ordered list: last detection
  detection-durations ; list: lengths of each session
  absence-durations ; list: lengths of no detections
  detection-durationsNN ; list: lengths of each session
  absence-durationsNN ; list: lengths of no detections
]
; SETUP STATIONS
; placed here, not with other setup functions BECAUSE
; STATION LOCATIONS SPECIFIED HERE!
to setup-stations
  ; SPECIFY STATION LOCATIONS WITH TWO LISTS TO IMPLEMENT A MATRIX
  let py-locations ( list 0 )
  ; stations along the birding trail, in patch coordinates
  let first-station 5 ; closest station to the road
  let station-separation 2 * human-mult * base-percept-patches + 1 ; no chance of detection by two stations
  let num-listening-stations 5 ; generate a pseudogeometric sequence with five stations
  let station-multiplier ( ( max-pxcor - first-station - station-separation) / ( num-listening-stations - 1 ) / station-separation ) ^ (
    1 / ( num-listening-stations - 1 ) )
  let px-locations n-values ( num-listening-stations ) [
    x -> round ( first-station + x * station-separation * station-multiplier ^ x ) ]
  let station-locations ( patch-set reduce sentence (
    map [ x -> map [ y -> patch x y ] py-locations ] px-locations ) )
  ; for bioacoustic monitoring replace the patch-set in the next line with appropriate pxcor and pycor values
  create-stations ( length px-locations ) * ( length py-locations )
  [
    set shape "person student"
    set size 10
    set color gray
    move-to one-of station-locations with [ 0 = count stations-here ]
    set sound ambient-level
    set percept human-mult * base-percept-patches
    set absent-tick 0
    set absent-tickNN 0
    set searchers-detected no-turtles
    set searchers-detectedNN no-turtles
    set sum-absent-noise 0
    set searchers-active [] ; must be lists to maintain alignments with firstick
    set searchers-firstick []
    set searchers-activeNN []
    set searchers-firstickNN []
    set sound-history []
    set detection-durations []
    set absence-durations []
    set detection-durationsNN []
    set absence-durationsNN []
    ; ?could? expand to keep detection and absence durations per searcher (excess detail?)
    if calc-noise [
      turtle-noise
      ; sound-history gets initialized by station-check
    ]; sets percept, sound, size, color
  ]
  station-check
  ask stations [
    set detection-durations []
    set absence-durations []
    set detection-durationsNN []
    set absence-durationsNN []
  ]
end

; UTILITY FUNCTIONS

; discrete equivalent of integration
to-report cumsum [ lst ]
  report butfirst reduce [ [ csum next-item ] -> lput ( next-item + last
    csum ) csum ] fput [0] lst
end ; used in noise sensitive resource settlement

; inverse of cumsum, discrete equivalent of differentiation
to-report diff [ lst ]
  report ( map [ [ z y ] -> z - y ] ( but-first lst ) ( but-last lst ) )
end ; may not need this: complements cumsum

; returns a list with the unique items from the input list
to-report unique [ lst ]
  report reduce [ [ uniq nxt ] ->
    ifelse-value member? nxt uniq [ uniq ] [ fput nxt uniq ] ] fput [] lst
end

; flatten nested lists
to-report unnest [ xs ] ; used in the BehaviorSpace reporters
  let ys reduce sentence xs
  report ifelse-value (reduce or map is-list? ys) [ unnest ys ] [ ys ]
end

; splits strings into words using delimiters
to-report str-split [ string delim ]
  ; split the string up into individual characters
  let characters fput [""] n-values ( length string ) [ a -> substring string a ( a + 1 ) ]
  ;  build words, cutting where the delimiter occurs
  let output reduce [ [ b c ] ->
    ifelse-value ( c = delim )
    [ lput "" b ]
    [ lput word last b c but-last b ]
  ] characters
  report output
end

; converting strings to values, flattens nested lists
to-report read-from-list [ x ]
  report ifelse-value is-list? x
    [ map read-from-list x ]
  [ read-from-string x ]
end

; bisection search: find the iterval covering val
to-report hash-idx [ val lst ]
  let bot 0
  let top  ( length lst ) - 1
  let mid floor ( ( top + bot ) / 2 )
  while [ not ( bot = mid ) ] [
    ifelse item mid lst <= val [
      set bot mid ] [
      set top mid ]
    set mid floor ( ( top + bot ) / 2 )
  ]
  report bot
end

; utility to displace a second vehicle from landing on a patch
to separate-vehicles
  if any? other vehicles-here [
    fd 0.9 + random-float 2 ; randomized the adjustment a bit relative to the Simple Traffic library model
    separate-vehicles
  ]
end ; exaggerates separation relative to what happens dynamically: legacy from Simple Traffic library model

; utility used for noise-sensitive resource placement
; NOTE: THE INPUT MUST BE SORTED
to-report pxcor-replicates [ sorted-pxcor-list ]
  let rslt reduce [
    [ sofar nxt ] ->  ( ifelse-value
      ( length sofar ) = 0 [ list nxt 1 ]
      nxt = ( first sofar ) [ replace-item 1 sofar ( item 1 sofar + 1 ) ]
      [ ( fput nxt fput 1 sofar ) ] ) ] fput [] sorted-pxcor-list
  report rslt
end ; reports a list of pxcor-count pairs for resource placement

; utility to setup-resources
to make-resource
  set hab "resource"
  set pcolor blue
  set quality random-float 100 ; not used at present
end

; NOISE SOURCE AND PROPAGATION FUNCTIONS

; get the noise(speed) prediction coefficients
to-report get-coefs [ file-name ]
  let vehicle-coefs []
  file-open file-name
  while [ not file-at-end? ] [
    let v-spec file-read-line
    set v-spec str-split v-spec "\t"
    set v-spec read-from-list v-spec
    set vehicle-coefs lput v-spec vehicle-coefs
  ]
  file-close
  report vehicle-coefs
end

; returns list of P^2 from a list of dB
to-report anti-dB [ dB-val-list ]
  report map [ x -> 10 ^ ( x / 10 ) ] dB-val-list
end

; ISO-9613 ground attenuation
to-report atten-ground [ lat-metrs height-metrs freqhz]
  let oneEdp50 1 - exp ( ( - lat-metrs ) / 50 )
  let oneE28dp2 1 - exp ( -2.8E-6 * lat-metrs ^ 2 )
  report ( ifelse-value ( freqhz < 100 )
    [ -1.5  ]
    ( freqhz >= 100 and freqhz < 200 )
    [ ( -1.5  + ground-hardness * ( 1.5 + 3 * exp ( -0.12 * ( height-metrs - 5 ) ^ 2 ) * oneEdp50 +
      5.7 * exp ( -0.09  * height-metrs ^ 2 ) * oneE28dp2 ) ) ]
    ( freqhz >= 200 and freqhz < 400 )
    [ -1.5 + ground-hardness * ( 1.5 + 8.6 * exp ( -0.09 * height-metrs ^ 2 ) * oneEdp50 ) ]
    ( freqhz >= 400 and freqhz < 800 )
    [ -1.5 + ground-hardness * ( 1.5 + 14.0 * exp ( -0.46 * height-metrs ^ 2 ) * oneEdp50) ]
    ( freqhz >= 800 and freqhz < 1600)
    [ -1.5 + ground-hardness * ( 1.5 + 5.0 * exp ( -0.9 * height-metrs ^ 2 ) * ( 1 - exp ( -1 * lat-metrs / 50 ) ) ) ]
    [ -1.5 * ( 1 - ground-hardness ) ] )
end

; ISO-9613 total attenuation, returns decibels
to-report iso-9613 [ lateral-meters frq ]
  let p0  101.325
  let tK0 293.15
  let slant-range sqrt ( ( height-noiz - height-rcvr ) ^ 2 + lateral-meters ^ 2 )
  let diverg-loss 20 * ( log ( slant-range / ref-distance ) 10 )
  let h-mole relative-humidity * 10 ^ ( -6.8346 * ( 273.16 / temp-kelvin ) ^ 1.261 + 4.6151) / ( atm-pressure-bar / p0 )
  let rel-freqO ( atm-pressure-bar / p0 ) * (24 + 4.04E4 * h-mole * ( 0.02 + h-mole ) / ( 0.391 + h-mole ) )
  let rel-freqN ( atm-pressure-bar / p0 ) * sqrt ( tK0 / temp-kelvin ) * ( 9 + 280 * h-mole * exp ( -4.17 * ( ( tK0 / temp-kelvin ) ^ ( 1.0 / 3.0 ) - 1 ) ) )
  set atten-absorp 8.686 * frq ^ 2 * ( 1.84E-11 * ( p0 / atm-pressure-bar ) * sqrt ( temp-kelvin / tK0 ) +
    					( tK0 / temp-kelvin ) ^ ( 5.0 / 2.0 ) * ( 0.01275 * exp ( -2239.1 / temp-kelvin ) /
      							( rel-freqO + ( frq ^ 2 / rel-freqO ) ) + 0.1068 * exp ( -3352 / temp-kelvin ) /
      							( rel-freqN + ( frq ^ 2 / rel-freqN ) )
    					)
  			)
  let q ifelse-value ( lateral-meters > ( 30 * ( height-rcvr + height-noiz ) ) )
  [ 1 - ( 30 * ( height-rcvr + height-noiz ) / lateral-meters ) ] [ 0.0 ]
  let atten-gnd-mid ifelse-value frq < 100 [ ( - 3 ) * q ^ 2 ]  [ ( - 3 ) * q * ( 1 - ground-hardness ) ]
  let atten-gnd-src atten-ground lateral-meters height-noiz frq
  let atten-gnd-rcv atten-ground lateral-meters height-rcvr frq
  report slant-range * atten-absorp + atten-gnd-src + atten-gnd-mid + atten-gnd-rcv + diverg-loss
end ; returns total attenuation in dB (checked)

; utility for creating the range-speed lookup table
; returns A-weighted p^2 results suitable for aggregation across vehicles
; SEEMS FINE, BUT SHOULD CHECK AGAIN TO CONFIRM
; WRONG VALUES BEING USED FOR CIRCLE SIZES AND COLORS
to-report fast-noise [ m-per-sec meters ]
  report ( reduce + ( reduce [ [ acc b ] -> ( map * acc b ) ]
    ( list aWt ( speed2spec ( m-per-sec ) ) ( anti-dB map [ frq -> ( - iso-9613 meters frq ) ] freqs ) ) ) )
end

; utility for interactive A-weighted attenuation calculations
; not used in the code
to-report fast-atten [ meters ]
  report 10 * log ( reduce + ( map * ( atten-interpolate meters ) aWt ) ) 10
end

; creates the range-speed lookup table for A-weighted, pressure-squared, received level
to make-noise-table [ r-points ]
  set speed-points n-values ( speed-max + 1 ) [ j -> j + 1 ]
  set speed-points fput speed-min speed-points ; avoids extrapolation below speed-min
  set d-speed-points diff speed-points
  set range-spd-p2 map [ rng -> map [ spd -> fast-noise spd rng ] speed-points ] r-points
end

; create lookup table for total attenuation during setup
to make-atten-table [ num-points ]
  set total-atten map [ x -> anti-dB x ] ( map [ frq -> map [ rng -> ( - iso-9613 rng frq ) ] range-points ] freqs )
  ; above creates list (by 1/3rd OB) of lists (by range), anti-dB works on the range lists
  ; iso9613 returns dB, which are converted to P^2 units so propagation calculations avoid log10 and 10^ conversions
end ; checked

to-report noise-interpolate [ mps meters ]
  let ixr hash-idx meters range-points
  let ixs hash-idx mps speed-points
  let r0  item ixr range-spd-p2
  let r1 item ( ixr + 1 ) range-spd-p2
  let spd-frac ( remainder mps 1 ) ^ src-pow
  let sval  ( 1 - spd-frac) * item ixs r0 + spd-frac * item ( ixs + 1 ) r0
  let rfrac ( meters - item ixr range-points ) / ( item ixr d-range-points )
  let rval ( 1 - rfrac ) + rfrac * ( item ixs r1 ) / ( item ixs r0 )
  report sval * rval
  ; interpolate for speed at inner bound
  ;
  ; will extrapolate beyond the largest value
  ; extrapolation below the smallest value does not work: prevented by speed-min
end ; checked

; bisection search for attenuation interval
; returns interpolated estimate of total attenuation by frequency
to-report atten-interpolate [ meters ]
  let ix hash-idx meters range-points
  report map [ fq -> item ix fq + (item ( ix + 1) fq - item ix fq ) * ( meters - item ix range-points )/
    ( item ( ix + 1 ) range-points - item ix range-points ) ] total-atten
  ; linear interpolation (will extrapolate)
end ; checked

; predict noise spectrum from speed
; power function predicting noise spectrum in p^2 units from speed in m/s
to-report speed2spec [ spd ]
  report (map * ( item 0 src-coefs ) ( map [ x -> spd ^ x ] item 1 src-coefs ) )
end ; checked

; calculate total noise received by a searcher
to-report noise-turtles-spec
  ; asked of searchers or stations, sums over vehicles
  ; assumes that min-pxcor is zero, max-pxcor is even, and min-pycor = ( - max-pycor )
  ; returns p^2 total noise spectrum for d-prime calculation
  let xcor-rcv xcor ; save the searcher coordinates
  let ycor-rcv ycor
  let tot-noiz ambi-spectrum ; p^2 units, energy summation
  ask vehicles [
    let nz-spek speed2spec speed ; p^2 units
    ; pxcor = midpoint aligns with pxcor = 0 column in the searcher/resource space
    let vycor ifelse-value
      xcor = ( mid-pxcor ) [ ycor ]
      [ ( xcor - mid-pxcor ) * world-height + ycor ]
    let euclid-2d sqrt (  ( meters-per-unitNL * xcor-rcv ) ^ 2 + ( vycor - ( meters-per-unitNL * ycor-rcv ) ) ^ 2 )
    ; virtual y has 1 meter patches, real y has 10 meter patches
    let vnoiz-incr ( map * nz-spek ( atten-interpolate euclid-2d ) ) ; nz-spek in p^2, euclid-2d a scalar
    set tot-noiz ( map + tot-noiz vnoiz-incr )
  ]
  ; tot-noiz in p^2 units
  ; accumulate noise spectrum (24 values) from all vehicles
  ; could use d-prime to determine audibility
  report tot-noiz
end

; calculates p^2 1/3rd OB noise + ambient spectrum for a patch assuming uniform traffic on the road
; could be used to influence settlement probabilities using d-prime criteria
to-report settlement-noise-spec [ x-patch ]
  let tot-noiz ambi-spectrum
  ; P^2 units, energy summation
  ; same spectrum at each point on the road, multiply by fractional vehicle per road patch
  let nz-spek ( map [ spkval -> spkval * meters-per-unitNL * num-vehicles / ( world-width * world-height ) ]
    speed2spec ( speed-limit / 3.6 ) )
  ; average noise output from each segment of road
  ask patches [
    ; calculates contributions with fractional vehicles on each patch of virtual road
    ; assumes that max-pxcor is even if min-pxcor is zero
    let vycor ifelse-value
      pxcor = ( mid-pxcor ) [ pycor ]
      [ ( pxcor - mid-pxcor ) * world-height + pycor ]
    ; pycor = 0 to simplify calculations, exact if min-pycor = - max-pycor
    if 0 = remainder pycor meters-per-unitNL [ ; one vehicle every meters-per-unitNL meters
      let euclid-dD sqrt ( ( meters-per-unitNL * x-patch ) ^ 2 + vycor ^ 2 )
      ; virtual y has 1 meter patches, real x has 10 meter patches
      let vnoiz-incr ( map * nz-spek ( atten-interpolate euclid-dD ) ) ; nz-spek in p^2, attenuation a scalar
      set tot-noiz ( map + tot-noiz vnoiz-incr )
      ; tot-noiz in p^2 units
      ; accumulate noise spectrum (24 values) from all vehicles
    ]
  ]
  report tot-noiz
  ; A-weight the spectrum and sum
end

; calculate total noise received by a searcher
to-report noise-turtles
  ; asked of searchers or stations, sums over vehicles
  ; assumes that min-pxcor is zero, max-pxcor is even, and min-pycor = ( - max-pycor )
  let xcor-rcv xcor ; save the searcher coordinates
  let ycor-rcv ycor
  ; let tot-noiz ambi-spectrum ; p^2 units, energy summation
  let tot-noiz 10 ^ (ambient-level / 10 ) ; simplified summation of A-weighted energy
  ask vehicles [
    ; let nz-spek speed2spec speed ; p^2 units
    ; pxcor = midpoint aligns with pxcor = 0 column in the searcher/resource space
    let vycor ifelse-value
      xcor = ( mid-pxcor ) [ ycor ]
      [ ( xcor - mid-pxcor ) * world-height + ycor ]
    let euclid-2d sqrt (  ( meters-per-unitNL * xcor-rcv ) ^ 2 + ( vycor - ( meters-per-unitNL * ycor-rcv ) ) ^ 2 )
    ; virtual y has 1 meter patches, real y has 10 meter patches
  ;  let vnoiz-incr ( map * nz-spek ( atten-interpolate euclid-2d ) ) ; nz-spek in p^2, euclid-2d a scalar
  ;  set tot-noiz ( map + tot-noiz vnoiz-incr )
    set tot-noiz tot-noiz + noise-interpolate speed euclid-2d
  ]
  ; tot-noiz in p^2 units
  ; accumulate noise spectrum (24 values) from all vehicles
  ; could use d-prime to determine audibility
  ; report ( reduce + ( map * tot-noiz aWt ) )
  report 10 * log tot-noiz 10
end

; calculates total A-weighted noise landing on a patch from uniform traffic on the road
to-report settlement-noise [ x-patch ]
  ; let tot-noiz ambi-spectrum
  let tot-noiz 10 ^ ( ambient-level / 10 ) ; simplified summation of A-weighted energy
  ; P^2 units, energy summation
  ; same spectrum at each point on the road, multiply by fractional vehicle per road patch
  ; let nz-spek ( map [ spkval -> spkval * meters-per-unitNL * num-vehicles / ( world-width * world-height ) ]
  ;   speed2spec ( speed-limit / 3.6 ) )
  ; average noise output from each segment of road
  ask patches [
    ; calculates contributions with fractional vehicles on each patch of virtual road
    ; assumes that max-pxcor is even if min-pxcor is zero
    let vycor ifelse-value
      pxcor = ( mid-pxcor ) [ pycor ]
      [ ( pxcor - mid-pxcor ) * world-height + pycor ]
    ; pycor = 0 to simplify calculations, exact if min-pycor = - max-pycor
    if 0 = remainder pycor meters-per-unitNL [ ; one vehicle every meters-per-unitNL meters
      let euclid-2d sqrt ( ( meters-per-unitNL * x-patch ) ^ 2 + vycor ^ 2 )
      set tot-noiz tot-noiz + noise-interpolate ( ( speed-limit / 3.6 ) * (
        meters-per-unitNL * num-vehicles / ( world-width * world-height ) ) )  euclid-2d
      ; virtual y has 1 meter patches, real x has 10 meter patches
      ; let vnoiz-incr ( map * nz-spek ( atten-interpolate euclid-dD ) ) ; nz-spek in p^2, attenuation a scalar
      ; set tot-noiz ( map + tot-noiz vnoiz-incr )
      ; tot-noiz in p^2 units
      ; accumulate noise spectrum (24 values) from all vehicles
    ]
  ]
  report tot-noiz
  ; report reduce + ( map * tot-noiz aWt )
  ; A-weight the spectrum and sum
end

; get noise exposure, set percept and visible indicators
to turtle-noise
  set sound noise-turtles
  set percept base-percept-patches * 10 ^ ( ( ambient-level - sound ) / 10 )
  if-else is-searcher? self [ ; change color and size of searchers, not stations
    let multiplier ( base-searcher-size * percept / base-percept-patches )
    set size max ( list 0.1 multiplier )
    set color max ( list 0 ( 4.2560859226518675 * ln multiplier ) ) ; 9.8 / ln 10, could use scale-color
  ] [ set percept percept * human-mult ] ; otherwise a station
end

; SETUP FUNCTIONS

to setup-constants
  set mid-pxcor ( max-pxcor - min-pxcor ) / 2
  set temp-kelvin temp-celsius + 273.15
  set meters-per-unitNL 10 ; 1 unit in NetLogo equals 10 meters in the ecological world
  set ref-distance 304.8 ; reference distance in meters for the noise spectra that yielded the fitted coefficients
  set num-ranges 100 ; width of the attenuation lookup table ( total-atten )
  let max-range sqrt ( ( ( world-width * world-height + 1 ) / 2 ) ^ 2 +
    ; maximum vycor value: last "+1" allows for -0.5 and + 0.5 at edges of wrapped axis
    ( meters-per-unitNL * ( max-pxcor + 0.5 ) ) ^ 2 + ( height-rcvr - height-noiz ) ^ 2 ) + 10
  ; vycor is in meters: not multiplied by meters-per-unitNL
  ; we have a linear array of road number of patches cells (meters)
  ; result in meters, "+ 10" ensures an endpoint for the linear interpolation
  let range-mult-incr max-range ^ ( 1 / num-ranges )
  set range-points n-values ( 1 + num-ranges ) [ j -> range-mult-incr ^ j ]
  set d-range-points diff range-points
  set ambient-levelP2 10 ^ ( ambient-level / 10 )
  set speed-min 1e-4
  set speed-max 27 ; 27 m/s max referenc speed for interpolation table and gray scaling
  set sspeed-patches searcher-speed / meters-per-unitNL
  set reflect-bias 0.3
  set num-resources round ( meters-per-unitNL ^ 2 * ( world-width * world-height ) / (
    meters-moved-per-resource * 2 * base-percept ) )
  set base-vehicles-hour 1000 * num-vehicles * speed-limit / world-width / world-height
  set noise-decorrelate-ticks ceiling ( 300 / sqrt ( speed-limit ^ 2 + searcher-speed ^ 2 ) )
  set accel-jitter 1e-2 ; 1% jitter of acceleration per tick
  set acc-jitt2 1 - ( accel-jitter / 2 )
  set kolr-decay 0.98 ; > 0 and < 1.0
  set base-percept-patches base-percept / meters-per-unitNL
  set base-searcher-size 2 * base-percept / meters-per-unitNL
  set base-visited-rate sspeed-patches * 2 * base-percept-patches * num-resources / ( world-width * world-height )
  set sum-visited 0
  set base-birdable 2 * base-percept-patches * human-mult / ( 2 * max-pycor + 1)
  set sum-birdable 0
  set freqs [ 25 31.5 40 50 63 80 100 125 160 200 250 315 400 500 630 800 1000 1250 1600 2000 2500 3150 4000 5000 ]
  set aWt map [ x -> 10 ^ ( x / 10 ) ] [ -44.7 -39.4 -34.6 -30.2 -26.2 -22.5 -19.1 -16.1 -13.4 -10.9 -8.6 -6.6
    -4.8 -3.2 -1.9 -0.8 0.0 0.6 1.0 1.2 1.3 1.2 1.0 0.5 ]
end

; mainly patch coloring, but effectively excludes resources from the road
to setup-patch
  ( ifelse pxcor = 0 [
    set pcolor orange
    set hab "road"
    ]; NOTE: no resources on the road
     ; pycor = min-pycor and
    ( abs (pxcor - mid-pxcor ) <
      max-pycor * meters-per-unitNL / world-height ) [
      set pcolor orange + 4.5
      set hab "virtualroad"
    ]
    [ set pcolor white ] ; no other patch setup at present
  )
end

; ambient and vehicle spectral setup
to setup-spectra
  set ambi-spectrum anti-dB ( n-values 24 [ j -> 12 - j ] )
  ; NOTE: artificial red spectrum, - 3 dB/octave
  let konst ambient-levelP2 / ( reduce + ( map * ambi-spectrum aWt ) )
  ; constant results in 0 dB A-weighted
  set ambi-spectrum map [ fval -> fval * konst ] ambi-spectrum
  ; shift spectrum upward to match ambient
  ; show  10 * log ( reduce + ( map * ambi-spectrum aWt ) ) 10 ; confirmation
  ; set veh-name user-one-of "Choose vehicle type" [ "Sedan" "Motorcycle" ]
  set src-coefs ifelse-value "sedan" = veh-name [ get-coefs "CarCoef2.tsv" ] [ get-coefs "MotoCoef2.tsv" ]
  set src-pow 2
end

; NMSim source speeds: 6.7056 11.1760 24.5872 m/s
to setup-vehicles
  if num-vehicles > world-width * world-height / 20 [
    user-message (word
      "There are too many vehicles for the amount of road. "
      "Please decrease the num-vehicles slider to below "
      ( world-width * world-height / 20 ) " and press the SETUP button again. "
      "The setup has stopped.")
    stop
  ]
  set-default-shape vehicles "car"
  create-vehicles num-vehicles [
    setxy random-pxcor random-ycor
    set heading 0
    set size 2
    set color gray + 4.5
    ; convert km/hr to m/s
    ; vspeed variability influences development of traffic congestion
    set vspeed-limit ( speed-limit / 3.6 ) *
    ( random-gamma ( 1 / ( speed-limit-SD ^ 2 ) ) ( 1 / ( speed-limit-SD ^ 2 ) ) )
    ; use mean of 1.0
    ; alpha = mean * mean / variance; lambda = 1 / (variance / mean)
    set speed vspeed-limit
    set speed-pps speed / meters-per-unitNL
    ; alpha = mean * mean / variance; lambda = 1 / (variance / mean)
    ; larger SD increases congestion
    separate-vehicles
  ]
  if vpass-probability < 1.0 [ repeat 1000 [ move-vehicles ] ] ; equilibrate traffic
end

to setup-resources ; two resources cannot land on the same patch, but no other constraint on proximity
  ifelse noise-affects-resources? = true and calc-noise
  [
    let noiz-selector n-values max-pxcor [ xm -> settlement-noise ( xm + 1 ) ] ; aggregate average noise for all pxcor values (except zero)
    set noiz-selector cumsum ( map [ nz -> ambient-levelP2 / nz ] noiz-selector )
    set noiz-selector fput 0 map [ x -> x / (last noiz-selector ) ] noiz-selector ; list from 0..1
    let rez-x-count pxcor-replicates sort map [ x -> hash-idx x noiz-selector ] n-values num-resources [ x -> random-float 1 ]
    foreach ( n-values ( length rez-x-count  / 2 ) [ x -> x ] ) [ x ->
      ask n-of ( item ( 2 * x + 1 ) rez-x-count ) patches with [
        ( ( pxcor = ( 1 + item ( 2 * x ) rez-x-count ) and ( hab != "road" ) ) ) ] [ make-resource ] ]
  ] [ ; resources placed at random
    ask n-of num-resources patches with [ hab != "road" ]
    [ make-resource ]
  ]
end

to setup-searchers
  create-searchers num-searchers
  [
    set shape "circle"
    move-to one-of patches with [ pcolor = white ]
    ; overdisperse to minimize artificial similarities from searchers placed nearby at random
    while [ 0.4 * sqrt ( world-width * ( world-height + 1 ) / num-searchers ) >
      min [ distance myself ] of other searchers ] [
      move-to one-of patches with [ pcolor = white ] ]
    set moving-to nobody
    set heard-not-visited no-patches
    set resources-visited no-patches
    set resources-nonoise no-patches
    set resourceNoise []
    set birderNoise []
    set birderX []
    set birdable-durations []
    set birdable-absences []
    set birdable-durationsNN []
    set birdable-absencesNN []
    set sound ambient-level
    set color 9.8
    set size 10
    set percept base-percept-patches
    if calc-noise [
      turtle-noise
      set sound-history ( list sound ) ; initialize with first exposure
    ]; sets percept, sound, size, color
    ifelse abs ycor < ( human-Mult * base-percept-patches ) [
      set birdable-lasttickNN 1
      ; positive value means start of birdable session
      ; if birdable session just started
      ifelse abs ycor < ( human-Mult * percept ) [
        set birdable-lasttick 1
        set sum-birdable sum-birdable + 1 ; global variable
      ][
        set birdable-lasttick ( - 1 )
      ]
    ][
      set birdable-lasttickNN ( - 1 )
      set birdable-lasttick ( - 1 )
    ]
  ]
end

to setup
  clear-all
  random-seed new-seed
  reset-ticks
  reset-timer
  setup-constants
  ask patches [ setup-patch ]
  setup-spectra
  setup-vehicles ; delay while traffic equilibrates
  set veh-per-hour 3600 * ( count vehicles ) * ( mean [ speed ] of vehicles ) / (
    world-width * world-height )
  ; make-atten-table num-ranges ; will be used in d-prime version
  make-noise-table range-points
  let max-dB 10 * log ( noise-interpolate speed-max 1 ) 10
  let max-whitened 4.8
  set vph-unblocked 3600 * ( count vehicles ) * ( ( mean [ vspeed-limit ] of vehicles ) ) / (
    world-width * world-height )
  print ( word "unblocked vehicles per hour: " precision vph-unblocked 2 )
  setup-searchers
  setup-resources
  setup-stations
  print ( word "model setup elapsed time (s): " timer )
  print ( word "birdable probability without noise: " precision base-birdable 4 )
  reset-timer
end

; MOVEMENT FUNCTIONS

; utility for move-vehicles
to-report caught-vehicles
  report vehicles with [
    xcor = [ xcor ] of myself and
    ycor > [ ycor ] of myself and
    ( ( ycor + speed-pps ) <
      ( [ ycor + speed-pps ]  of myself ) ) ]
  ; can calculate even if cannot make this move without wraparound
end

to move-vehicles
  let sorted-vehicles sort-on [ xcor * ( 2 * max-pycor + 1 ) + ycor ] vehicles
  ; ESSENTIAL: ensures predictable order of processing to avoid ambiguities in overtaken calculations
  foreach sorted-vehicles [ ag ->
    ask ag [
      let overtaken caught-vehicles
      ifelse ( any? overtaken ) and ( random-float 1 > vpass-probability ) [
        let nearest min-one-of overtaken [ ycor ]
        set ycor max ( list ycor
          ( [ ycor - 2 * speed-pps ] of nearest ) )
        ; the " * 2 " term introduces a speed-dependent gap: two second safe following rule
        set speed max ( list speed-min ( ( [ speed ] of nearest ) - excess-brake / 3.6 ) )
        set speed-pps speed / meters-per-unitNL
        ; random terms ensures that two vehicles overtaking the same vehicle do not decelerate to the same location and speed
      ] [
        if-else can-move? ( speed-pps ) [
          fd speed-pps
        ] [
          let tmp-patches ycor + ( speed-pps ) - max-pycor - 0.5 ; what will be moved in from the bottom margin
          set xcor ifelse-value xcor < max-pxcor [ xcor + 1 ] [ 0 ]
          set ycor min-pycor - 0.5 + tmp-patches
        ]
        ; add acceleration after movement
        set speed min ( list vspeed-limit ( speed + acceleration * ( acc-jitt2 + random-float accel-jitter ) ) )
        set speed-pps speed / meters-per-unitNL
      ]
    ]
  ] ; foreach sorted vehicle
end

; check stations
to station-check ; assumes human-mult >=0: speeds up execution
  ask stations [
    if calc-noise [
      turtle-noise
      if 0 = ticks mod noise-decorrelate-ticks [ set sound-history lput sound sound-history ] ; periodic update
    ]
    let searchers-inrangeNN ( searchers in-radius ( human-mult * base-percept-patches ) )
    let searchers-inrange searchers-inrangeNN in-radius percept ; station percept = searchers' percept * human-mult
    ifelse any? searchers-inrangeNN [ ; some searchers in nonoise range
      if empty? searchers-activeNN [ set absence-durationsNN lput ( ticks - absent-tickNN ) absence-durationsNN ]
      ask searchers-inrangeNN with [ not member? self [ searchers-activeNN ] of myself ] [ ; not an error if no-searchers
        ask myself [ set searchers-activeNN lput myself searchers-activeNN ]
        ask myself [ set searchers-firstickNN lput ticks searchers-firstickNN ]
        ask myself [ set searchers-detectedNN (turtle-set myself searchers-detectedNN ) ] ; NOTE SHIFT IN MYSELF MEANING
      ] ; added new searchers and ticks
      if any? searchers-inrange [
        if empty? searchers-active [ set absence-durations lput ( ticks - absent-tick ) absence-durations ]
        set color sky
        ask searchers-inrange with [ not member? self [ searchers-active ] of myself] [
          ask myself [ set searchers-active lput myself searchers-active ] ; lists
          ask myself [ set searchers-firstick lput ticks searchers-firstick ]
          ask myself [ set searchers-detected ( turtle-set myself searchers-detected ) ]
        ] ; added new searchers and ticks
      ]
    ] [ ; else no searchers in noiseless range
      if not empty? searchers-activeNN [
        set absent-tickNN ticks
        ; save tick when last searcher moves out of range
        ; searchers-active and firstick will get emptied below
      ]
    ]
    if not any? searchers-inrange [
      set sum-absent-noise sound + sum-absent-noise
      if not empty? searchers-active [
        set color grey
        set absent-tick ticks
        ; save tick when last searcher moves out of range
        ; searchers-active and firstick will get emptied below
      ]
    ]
    ; remove searchers who moved out of nonoise range and add their detection durations
    foreach ( filter [ sh -> not member? sh searchers-inrangeNN ] searchers-activeNN ) [ schr ->
      ; calculate duration of detection for that searcher and remove
      let ix position schr searchers-activeNN
      set detection-durationsNN lput ( ticks - item ix searchers-firstickNN ) detection-durationsNN
      set searchers-activeNN remove-item ix searchers-activeNN
      set searchers-firstickNN remove-item ix searchers-firstickNN
    ]
    ; remove searchers who moved out of range and add their detection durations
    foreach ( filter [ sh -> not member? sh searchers-inrange ] searchers-active ) [ schr ->
      ; calculate duration of detection for that searcher and remove
      let ix position schr searchers-active
      set detection-durations lput ( ticks - item ix searchers-firstick ) detection-durations
      set searchers-active remove-item ix searchers-active
      set searchers-firstick remove-item ix searchers-firstick
    ]
  ] ; ask stations
end

to birdable-check ;
;  show ( word "ycor: " precision ycor 2 " hmPrcpt: " precision ( human-Mult * percept ) 2 " lasttick: " birdable-lasttick )
  ifelse abs ycor < ( human-Mult * base-percept-patches ) [
    if 0 > birdable-lasttickNN [ ; negative value means just moved in range
      set birdable-absencesNN ( ; add new absence duration
        lput ( ticks + birdable-lasttickNN ) birdable-absencesNN )
      set birdable-lasttickNN ticks ; positive value means start of birdable session
    ] ; if birdable session just started
    ifelse abs ycor < ( human-Mult * percept ) [
      if 0 > birdable-lasttick [ ; negative value, just moved in range
        set birderNoise lput sound birderNoise
        set birderX lput xcor birderX
        set birdable-absences (
          lput ( ticks + birdable-lasttick ) birdable-absences )
        set birdable-lasttick ticks ; positive value, start of birdable session
      ]
      set sum-birdable sum-birdable + 1
      ask ( patch pxcor 0 ) [ set pcolor cyan ]
    ] [ ; else not within masked birding range
      if 0 < birdable-lasttick [ ; positive, just departed
        set birdable-durations (
          lput ( ticks - birdable-lasttick ) birdable-durations )
        set birdable-lasttick ( - ticks ) ; negative signals when absence started
      ]
    ] ; masked birder detection
  ] [ ; else not within noiseless birding range
    if 0 < birdable-lasttickNN [ ; if positive, then just ended a birdable session
      set birdable-durationsNN (
        lput ( ticks - birdable-lasttickNN ) birdable-durationsNN )
      set birdable-lasttickNN ( - ticks ) ; negative signals when absence started
    ]
    if 0 < birdable-lasttick [ ; if positive, then just ended a birdable session
      set birdable-durations (
        lput ( ticks - birdable-lasttick ) birdable-durations )
      set birdable-lasttick ( - ticks ) ; negative signals when absence started
    ]
    ask ( patch pxcor 0 ) [ set pcolor yellow ] ;
  ]
end

to move-searcher
  ifelse moving-to != nobody or any? heard-not-visited [ ; approach phase
    set color lime ;
    if moving-to = nobody [
      set moving-to min-one-of heard-not-visited [ distance myself ] ]
    ; NOT USED AT PRESENT: sort-by [ [ a b ] ->  ( [ quality ] of a ) > ( [ quality ] of b ) ]
    set heard-not-visited heard-not-visited with [ self != [ moving-to ] of myself ]
    face moving-to
    ifelse distance moving-to < sspeed-patches [
      move-to moving-to ; land on the resource
      set resources-visited ( patch-set resources-visited patch-here )
      set sum-visited sum-visited + 1
      set moving-to min-one-of heard-not-visited [ distance myself ]
      if moving-to = nobody [ set color 9.8 ]
    ] [fd sspeed-patches] ; else move toward
  ] [ ; else moving
      ; if edge reached, try random reorientations until can move
    set heading heading + random-normal 0 search-turn-sd ; deviate from course and proceed
    if not can-move? sspeed-patches [ ; boundary code
      ifelse abs ( ycor + dy ) > max-pycor + 0.5 [
        let rand-frac random-float 1.0
        let dyy ( - dy ) * rand-frac + ( 1 - rand-frac ) * reflect-bias
        set heading atan ( sqrt ( 1 - dyy ^ 2) * dx / abs dx ) dyy
        let xtst xcor + dx
        if xtst < ( - 0.5 ) or xtst > max-pxcor + 0.5 [
          set heading atan ( - dy ) ( - dx ) ; reverse course, reflecting about the 45 degree line
        ]
      ] [
        let xtst xcor + dx
        if xtst < ( - 0.5 ) or xtst > max-pxcor + 0.5 [
          let rand-frac random-float 1.0
          let dxx ( - dx ) * rand-frac + ( 1 - rand-frac ) * reflect-bias
          set heading atan dxx ( sqrt ( 1 - dxx ^ 2) * dy / abs dy )
          if abs ( ycor + dy ) > max-pycor + 0.5 [
            set heading atan ( - dy ) ( - dx ) ; reverse course, reflecting about the 45 degree line
          ]
        ]
      ]
    ]
    fd sspeed-patches
  ] ; ifelse end approach-movement
end

; states: moving to resource, searching
to update-searchers
  ask searchers[
    if calc-noise [
      turtle-noise
      if 0 = ticks mod noise-decorrelate-ticks [ set sound-history lput sound sound-history ] ; periodic update
    ] ; sets sound, percept, color, size
    birdable-check
    move-searcher
    ; check for resources (could be packaged as a procedure: "check-resources"
    let patches-inrange ( patches in-radius base-percept-patches with [ hab = "resource" ] )
    if no-patches != patches-inrange [
      set resources-nonoise ( patch-set resources-nonoise patches-inrange ) ]
    set patches-inrange ( patches-inrange in-radius percept ) with [
      not member? self [ resources-visited ] of myself and
      not member? self [ heard-not-visited ] of myself ]
    if no-patches != patches-inrange [
      set resourceNoise ( sentence resourceNoise n-values count patches-inrange [ sound ]) ; save sound level(s)
      set heard-not-visited ( patch-set patches-inrange heard-not-visited )
    ]
  ] ; ask searchers
end

to go
  tick
  ; this command creats the fading tails for each searcher on the birding path, blending towards white
  ask patches with [ pycor = 0 ] [ set pcolor kolr-decay * pcolor + ( 1 - kolr-decay ) * ( 4.9 + 5 * floor ( pcolor / 5 ) ) ]
  move-vehicles
  update-searchers
  station-check
  ; for GUI monitor
  let vph-now  3600 * ( count vehicles ) * ( mean [ speed ] of vehicles ) / (
    world-width * world-height )
  ; running median, more smoothing with increasing ticks
  let vph-adjust vph-unblocked / ticks ; lengthens averaging time as simulation proceeds
  set veh-per-hour ifelse-value veh-per-hour > vph-now [ veh-per-hour - vph-adjust ] [ veh-per-hour + vph-adjust ]
end

;to settle ;at end of simulations, searchers choose a resource that is the highest quality they observed that is not already chosen by another searcher
;  ask searchers [
;    set color green
;    ifelse any? resources-visited with [not any? searchers-here] ; searchers-here is an agentset of all searchers on the patch
;    [move-to max-one-of resources-visited with [not any? searchers-here][quality]]
;    [die]
;  ]
;end
@#$#@#$#@
GRAPHICS-WINDOW
250
10
1461
922
-1
-1
3.0
1
10
1
1
1
0
0
0
1
0
400
-150
150
1
1
1
ticks
30.0

BUTTON
95
180
150
213
NIL
go
T
1
T
OBSERVER
NIL
NIL
NIL
NIL
0

SLIDER
0
300
33
461
num-vehicles
num-vehicles
25
2000
250.0
25
1
NIL
VERTICAL

SLIDER
140
300
173
460
excess-brake
excess-brake
0
30
5.0
0.25
1
km/hr
VERTICAL

SLIDER
105
300
138
460
acceleration
acceleration
0
.1
0.05
.005
1
m/s^2
VERTICAL

SLIDER
65
515
98
661
temp-celsius
temp-celsius
-20
30
20.0
1
1
Celsius
VERTICAL

SLIDER
98
515
131
660
atm-pressure-bar
atm-pressure-bar
60
105
101.0
1
1
Bar
VERTICAL

SLIDER
133
515
166
660
relative-humidity
relative-humidity
0
100
60.0
1
1
%
VERTICAL

SLIDER
168
515
201
660
ground-hardness
ground-hardness
0
1
0.5
0.05
1
NIL
VERTICAL

SLIDER
-5
515
28
660
height-noiz
height-noiz
0.5
1000
0.5
0.5
1
meters
VERTICAL

SLIDER
30
515
63
660
height-rcvr
height-rcvr
0.1
10
1.6
0.1
1
meters
VERTICAL

SLIDER
210
10
243
175
human-mult
human-mult
1
10
4.0
.1
1
NIL
VERTICAL

SLIDER
175
10
208
175
base-percept
base-percept
0
500
50.0
1
1
meters
VERTICAL

SLIDER
140
10
173
175
ambient-level
ambient-level
0
50
25.0
1
1
dB
VERTICAL

SLIDER
0
10
33
215
meters-moved-per-resource
meters-moved-per-resource
10
1000
200.0
10
1
NIL
VERTICAL

SWITCH
0
215
250
248
noise-affects-resources?
noise-affects-resources?
1
1
-1000

SLIDER
35
300
68
460
speed-limit
speed-limit
2
100
40.0
1
1
km/hr
VERTICAL

SLIDER
70
300
103
460
speed-limit-SD
speed-limit-SD
0
.2
0.2
0.01
1
NIL
VERTICAL

SLIDER
175
300
208
460
vpass-probability
vpass-probability
0
1
0.1
0.05
1
NIL
VERTICAL

SWITCH
-5
665
170
698
calc-noise
calc-noise
0
1
-1000

MONITOR
0
465
130
510
Median vehicles/hour
veh-per-hour
2
1
11

PLOT
5
715
245
835
Histogram of vehicle speed
meters per second
# vehicles
0.0
30.0
0.0
2.0
true
false
"set-histogram-num-bars 25\n" ""
PENS
"default" 1.0 0 -16777216 true "" "histogram [ speed ] of vehicles"

MONITOR
135
465
245
510
Mean speed (m/s)
mean [ speed ] of vehicles
1
1
11

SLIDER
35
10
68
175
num-searchers
num-searchers
0
100
40.0
1
1
animals
VERTICAL

SLIDER
105
10
138
176
search-turn-sd
search-turn-sd
0
10
3.0
1
1
degrees
VERTICAL

SLIDER
70
10
103
175
searcher-speed
searcher-speed
0.1
10
1.0
0.1
1
m/s
VERTICAL

MONITOR
172
665
242
710
ticks / hr
3600 * ticks / timer
0
1
11

MONITOR
0
250
137
295
meters per resource
ticks * num-searchers * searcher-speed / sum-visited
2
1
11

MONITOR
135
250
250
295
Birdable Probability
sum-birdable / ticks / num-searchers
4
1
11

CHOOSER
155
170
247
215
veh-name
veh-name
"sedan" "motorcycle"
0

BUTTON
40
180
95
213
NIL
Setup
NIL
1
T
OBSERVER
NIL
NIL
NIL
NIL
1

@#$#@#$#@
## WHAT IS IT?
This code models the masking effects of road noise on a species ("searchers") that detects resources by listening for their sounds. The Simple Traffic Model in the NetLogo library was the starting point for the vehicle movements, to enable this model to investigate the potential effects of congestion on noise exposure.
There is an overall speed limit, and each car has a speed limit that differs from the global value (with some exceeding it). Each car follows a simple set of rules: it slows down (decelerates) if it sees a car close ahead, and speeds up (accelerates) if it doesn't see a car ahead. Congestion is caused by the excessive deceleration of drivers and limited passing probabilities. Vehicles are identical, yet the level and spectral shape of their noise output changes with speed. Sedan and motorcycle noise output and spectra were drawn from 1/3rd octave band data packaged with the NMSim noise model (Wyle Laboratories and Blue Ridge Research and Consulting). 1/3rd OB spectra at three speeds were used to fit a power-law function for each spectral band. The power-law coefficients are imported into NetLogo to predict noise band level as a function of speed. _Note: this does not account for increased engine noise during acceleration._ In addition to different spectral shapes, the motorcycle noise output is about twice that of sedans.
Searchers move at a constant speed with Gaussian deviations from their previous course until a resource falls with their listening area (perceptual space). This happens because they move toward the resource, the noise level falls, or both. When a resources is heard, the searcher orients towards the resource and move without course deviations until they land on the patch. Then they move toward the next resource they heard (perfect memory) or resume searching along the course that took them to the patch (with deviations). When a searcher is moving towards a resource their color changes to lime green.
Each searcher's perceptual space is portrayed as a circle whose size shows the listening area and whos gray scale value is proportional to noise exposure in decibels (a logarithmic scale). The audibility of searchers to listeners along a path located at ycor=0 is calculated by how often the searcher is within the masked detection distance of listeners on the path (path listeners have a noise-free perception distance that is a multiple of the searcher's perception distance). The path also contains listening stations, which can be used to investigate bioacoustic monitoring performance. Stations are stationary. They keep track of how many searchers pass within their masked detection range.
Noise sources and propagation are specified in 1/3rd octave bands from 25 to 5000 Hz. Noise propagation is implemented using ISO-9613 procedures (parts 1 and 2). Procedures for implementing barriers or terrain shielding are not included. Masking is calculated from the ratio of ambient to ambient + noise sound levels, using A-weighting to sum sound energy across 1/3rd octave bands before calculating the masking coefficient.
The patches in the model play two independent roles. As displayed, they form a matrix of habitat in two dimensions. Searchers move within this matrix, to detect and visit resources that are located on some patches. All four edges of the habitat are hard boundaries. When a searcher's next move would place them outside the bounds of the simulation, their course is reflected forward from their present course with a randomized bias towards an 18 degree departure heading (relative to the boundary). This randomized departure procedure was found to reduced edge artifacts during model development. The road's location in the ecological habitat is displayed as a dark orange line on the left edge. The resources searchers listen for are placed randomly, except that they cannot occur on the road.
For vehicles, the matrix of patches functions differently. All of the patches are stacked -- column-wise -- to approximate an indefintely long road that has the ecological habitat adjacent to its center. The patches on this virtual road that correspond to the orange line in the ecological habitat are marked by pale orange in the central columns. Columns to the left of this pale orange band represent road segments approaching the ecological habitat. Columns to the right represent departing road segments. Vehicles transiting beyond the top of one column reappear at the bottom of the column to the right. Vehicles exiting the top of the rightmost column reappear at the bottom of the leftmost column. At present the vehicle size and light grey color help focus attention on bioacoustic dynamics, but on close inspection the vehicles can be seen moving upward on the screen. The _setup-vehicles_ procedure can be modified to enhance vehicle visibility if you want to focus on traffic dynamics.
Due to intensive noise propagation computations for each source-receiver pair, the model's speed is controlled by the product of the number of vehicles times the number of searchers and the number of stations. A switch to turn off noise computations is provided to rapidly simulate traffic dynamics and noise-free bioacoustic performance.
## HOW TO USE IT
Select slider values for your scenario. For traffic, setting the probability of passing to 1.0 will eliminate congestion, resulting in the free movement of vehicles.
Click the setup button to initialize vehicles, resources, and searchers. There will a delay while the setup procedure simulates traffic to roughly equilibrate congestion on the road before the ecological accounting begins.
Click the go button to begin the simulation.
## THINGS TO NOTICE
The listening areas of the searchers will change size and grey scale value based on their noise exposure: proximity the road, number of nearby vehicles, and vehicle speeds. Noise exposure will change smoothly in most situations, but in some scenarios you may observe sudden changes in noise exposure when a nearby vehicle decelerates upon overtaking a vehicle in front. You will observe differences in noise exposure -- especially for searchers near the road on the left edge -- between the bottom and top of the habitat. This is due to asymmetries in the numbers of vehicles approaching or departing the center of the road and habitat.
Summaries of resources detected and birdable probabilities are reported. Compare these with the noise-free values reported in the Command Center window at startup.
Summaries of traffic flow are presented with a histogram of vehicle speeds, the mean speed of the vehicles, and a running median of the vehicles per hour (a measure of traffic that is widely reported by state Departments of Transportation for roads in the United States).
## THINGS TO TRY?
What differences to you observe due to congestion? Decreasing the _vpass-probability_ (or increasing the _excess-brake_ or _speed-limit-SD_) will increase congestion. If you do not change the number of vehicles, this will reduce speeds (reducing noise outputs) and result in larger gaps in traffic. How much of an ecological effect do you observe?
Taking this one step further, what happens if you increase the number of vehicles to roughly equalize the _Median vehicles/hour_ monitor during simulations? Are ecological effects solely dependent on the traffic rate (vehicles/hour) regardless of their speed?
More generally, are ecological effects solely dependent on total noise exposure? Does it matter how that noise is packaged (noise per vehicle, density of vehicles, speed of vehicles)? For example, motorcycles are about twice as noisy as sedans. Do simulations with half as many motorcycles as sedans yield the same outcomes?
## EXTENDING THE MODEL?
In this version, a few _stations_ are included to demonstrate the potential to explore bioacoustic monitoring performance at different levels of road traffic. The _setup-stations_ procedure is placed near the top of the code to make it easier to implement different arrangements of monitoring stations. Consider contrasts in overall performance between larger networks of less sensitive stations and smaller networks of more sensitive stations. Is the number of individuals detected strictly a function of the total area covered by all units and duration of the deployment? What happens if you increase the _search-turn-SD_ of the searchers, such that their movements are more localized?
Natural sounds, especially the accidental sounds produced by movements, are not present continuously. How are searcher movements, foraging efficiency, and noise impacts changed when resources are only audible intermittently. Does it matter whether audible cues are periodically or randomly available?
Many questions can be explored by introducing behavioral interactions between vehicles and searchers:

  1. What happens to traffic congestion if drivers slow down when they can see a searcher? What happens to the noise exposures of nearby searchers when this occurs?
  2. What happens to search efficiency if searchers bias their movements away from vehicle noise?
  3. If we move the road to the center of the habitat, how does noise avoidance affect road crossing rates?
  4. If we add the possibility of vehicle-searcher collisions, how does noise avoidance affect road mortality? How does changing the speeds and noise outputs of vehicles affect road crossing rates and mortality?

The 1/3rd octave band framework of sound modeling suggests a potential transition away from A-weighted detection calculations to implement a procedure informed by psychoacoustics, like "d-prime." The model could be tuned by adjusting the frequency bases of the band-level calculations to match the "critical bands" of taxa other than humans.
@#$#@#$#@
default
true
0
Polygon -7500403 true true 150 5 40 250 150 205 260 250

airplane
true
0
Polygon -7500403 true true 150 0 135 15 120 60 120 105 15 165 15 195 120 180 135 240 105 270 120 285 150 270 180 285 210 270 165 240 180 180 285 195 285 165 180 105 180 60 165 15

arrow
true
0
Polygon -7500403 true true 150 0 0 150 105 150 105 293 195 293 195 150 300 150

bird
false
0
Polygon -7500403 true true 135 165 90 270 120 300 180 300 210 270 165 165
Rectangle -7500403 true true 120 105 180 237
Polygon -7500403 true true 135 105 120 75 105 45 121 6 167 8 207 25 257 46 180 75 165 105
Circle -16777216 true false 128 21 42
Polygon -7500403 true true 163 116 194 92 212 86 230 86 250 90 265 98 279 111 290 126 296 143 298 158 298 166 296 183 286 204 272 219 259 227 235 240 241 223 250 207 251 192 245 180 232 168 216 162 200 162 186 166 175 173 171 180
Polygon -7500403 true true 137 116 106 92 88 86 70 86 50 90 35 98 21 111 10 126 4 143 2 158 2 166 4 183 14 204 28 219 41 227 65 240 59 223 50 207 49 192 55 180 68 168 84 162 100 162 114 166 125 173 129 180

box
false
0
Polygon -7500403 true true 150 285 285 225 285 75 150 135
Polygon -7500403 true true 150 135 15 75 150 15 285 75
Polygon -7500403 true true 15 75 15 225 150 285 150 135
Line -16777216 false 150 285 150 135
Line -16777216 false 150 135 15 75
Line -16777216 false 150 135 285 75

bug
true
0
Circle -7500403 true true 96 182 108
Circle -7500403 true true 110 127 80
Circle -7500403 true true 110 75 80
Line -7500403 true 150 100 80 30
Line -7500403 true 150 100 220 30

butterfly
true
0
Polygon -7500403 true true 150 165 209 199 225 225 225 255 195 270 165 255 150 240
Polygon -7500403 true true 150 165 89 198 75 225 75 255 105 270 135 255 150 240
Polygon -7500403 true true 139 148 100 105 55 90 25 90 10 105 10 135 25 180 40 195 85 194 139 163
Polygon -7500403 true true 162 150 200 105 245 90 275 90 290 105 290 135 275 180 260 195 215 195 162 165
Polygon -16777216 true false 150 255 135 225 120 150 135 120 150 105 165 120 180 150 165 225
Circle -16777216 true false 135 90 30
Line -16777216 false 150 105 195 60
Line -16777216 false 150 105 105 60

car
false
0
Polygon -7500403 true true 180 0 164 21 144 39 135 60 132 74 106 87 84 97 63 115 50 141 50 165 60 225 150 300 165 300 225 300 225 0 180 0
Circle -16777216 true false 180 30 90
Circle -16777216 true false 180 180 90
Polygon -16777216 true false 80 138 78 168 135 166 135 91 105 106 96 111 89 120
Circle -7500403 true true 195 195 58
Circle -7500403 true true 195 47 58

circle
false
0
Circle -7500403 true true 0 0 300

circle 2
false
0
Circle -7500403 true true 0 0 300
Circle -16777216 true false 30 30 240

cow
false
0
Polygon -7500403 true true 200 193 197 249 179 249 177 196 166 187 140 189 93 191 78 179 72 211 49 209 48 181 37 149 25 120 25 89 45 72 103 84 179 75 198 76 252 64 272 81 293 103 285 121 255 121 242 118 224 167
Polygon -7500403 true true 73 210 86 251 62 249 48 208
Polygon -7500403 true true 25 114 16 195 9 204 23 213 25 200 39 123

cylinder
false
0
Circle -7500403 true true 0 0 300

dot
false
0
Circle -7500403 true true 90 90 120

face happy
false
0
Circle -7500403 true true 8 8 285
Circle -16777216 true false 60 75 60
Circle -16777216 true false 180 75 60
Polygon -16777216 true false 150 255 90 239 62 213 47 191 67 179 90 203 109 218 150 225 192 218 210 203 227 181 251 194 236 217 212 240

face neutral
false
0
Circle -7500403 true true 8 7 285
Circle -16777216 true false 60 75 60
Circle -16777216 true false 180 75 60
Rectangle -16777216 true false 60 195 240 225

face sad
false
0
Circle -7500403 true true 8 8 285
Circle -16777216 true false 60 75 60
Circle -16777216 true false 180 75 60
Polygon -16777216 true false 150 168 90 184 62 210 47 232 67 244 90 220 109 205 150 198 192 205 210 220 227 242 251 229 236 206 212 183

fish
false
0
Polygon -1 true false 44 131 21 87 15 86 0 120 15 150 0 180 13 214 20 212 45 166
Polygon -1 true false 135 195 119 235 95 218 76 210 46 204 60 165
Polygon -1 true false 75 45 83 77 71 103 86 114 166 78 135 60
Polygon -7500403 true true 30 136 151 77 226 81 280 119 292 146 292 160 287 170 270 195 195 210 151 212 30 166
Circle -16777216 true false 215 106 30

flag
false
0
Rectangle -7500403 true true 60 15 75 300
Polygon -7500403 true true 90 150 270 90 90 30
Line -7500403 true 75 135 90 135
Line -7500403 true 75 45 90 45

flower
false
0
Polygon -10899396 true false 135 120 165 165 180 210 180 240 150 300 165 300 195 240 195 195 165 135
Circle -7500403 true true 85 132 38
Circle -7500403 true true 130 147 38
Circle -7500403 true true 192 85 38
Circle -7500403 true true 85 40 38
Circle -7500403 true true 177 40 38
Circle -7500403 true true 177 132 38
Circle -7500403 true true 70 85 38
Circle -7500403 true true 130 25 38
Circle -7500403 true true 96 51 108
Circle -16777216 true false 113 68 74
Polygon -10899396 true false 189 233 219 188 249 173 279 188 234 218
Polygon -10899396 true false 180 255 150 210 105 210 75 240 135 240

house
false
0
Rectangle -7500403 true true 45 120 255 285
Rectangle -16777216 true false 120 210 180 285
Polygon -7500403 true true 15 120 150 15 285 120
Line -16777216 false 30 120 270 120

leaf
false
0
Polygon -7500403 true true 150 210 135 195 120 210 60 210 30 195 60 180 60 165 15 135 30 120 15 105 40 104 45 90 60 90 90 105 105 120 120 120 105 60 120 60 135 30 150 15 165 30 180 60 195 60 180 120 195 120 210 105 240 90 255 90 263 104 285 105 270 120 285 135 240 165 240 180 270 195 240 210 180 210 165 195
Polygon -7500403 true true 135 195 135 240 120 255 105 255 105 285 135 285 165 240 165 195

line
true
0
Line -7500403 true 150 0 150 300

line half
true
0
Line -7500403 true 150 0 150 150

pentagon
false
0
Polygon -7500403 true true 150 15 15 120 60 285 240 285 285 120

person
false
0
Circle -7500403 true true 110 5 80
Polygon -7500403 true true 105 90 120 195 90 285 105 300 135 300 150 225 165 300 195 300 210 285 180 195 195 90
Rectangle -7500403 true true 127 79 172 94
Polygon -7500403 true true 195 90 240 150 225 180 165 105
Polygon -7500403 true true 105 90 60 150 75 180 135 105

person student
false
0
Polygon -13791810 true false 135 90 150 105 135 165 150 180 165 165 150 105 165 90
Polygon -7500403 true true 195 90 240 195 210 210 165 105
Circle -7500403 true true 110 5 80
Rectangle -7500403 true true 127 79 172 94
Polygon -7500403 true true 105 90 120 195 90 285 105 300 135 300 150 225 165 300 195 300 210 285 180 195 195 90
Polygon -1 true false 100 210 130 225 145 165 85 135 63 189
Polygon -13791810 true false 90 210 120 225 135 165 67 130 53 189
Polygon -1 true false 120 224 131 225 124 210
Line -16777216 false 139 168 126 225
Line -16777216 false 140 167 76 136
Polygon -7500403 true true 105 90 60 195 90 210 135 105

plant
false
0
Rectangle -7500403 true true 135 90 165 300
Polygon -7500403 true true 135 255 90 210 45 195 75 255 135 285
Polygon -7500403 true true 165 255 210 210 255 195 225 255 165 285
Polygon -7500403 true true 135 180 90 135 45 120 75 180 135 210
Polygon -7500403 true true 165 180 165 210 225 180 255 120 210 135
Polygon -7500403 true true 135 105 90 60 45 45 75 105 135 135
Polygon -7500403 true true 165 105 165 135 225 105 255 45 210 60
Polygon -7500403 true true 135 90 120 45 150 15 180 45 165 90

square
false
0
Rectangle -7500403 true true 30 30 270 270

square 2
false
0
Rectangle -7500403 true true 30 30 270 270
Rectangle -16777216 true false 60 60 240 240

star
false
0
Polygon -7500403 true true 151 1 185 108 298 108 207 175 242 282 151 216 59 282 94 175 3 108 116 108

target
false
0
Circle -7500403 true true 0 0 300
Circle -16777216 true false 30 30 240
Circle -7500403 true true 60 60 180
Circle -16777216 true false 90 90 120
Circle -7500403 true true 120 120 60

tree
false
0
Circle -7500403 true true 118 3 94
Rectangle -6459832 true false 120 195 180 300
Circle -7500403 true true 65 21 108
Circle -7500403 true true 116 41 127
Circle -7500403 true true 45 90 120
Circle -7500403 true true 104 74 152

triangle
false
0
Polygon -7500403 true true 150 30 15 255 285 255

triangle 2
false
0
Polygon -7500403 true true 150 30 15 255 285 255
Polygon -16777216 true false 151 99 225 223 75 224

truck
false
0
Rectangle -7500403 true true 4 45 195 187
Polygon -7500403 true true 296 193 296 150 259 134 244 104 208 104 207 194
Rectangle -1 true false 195 60 195 105
Polygon -16777216 true false 238 112 252 141 219 141 218 112
Circle -16777216 true false 234 174 42
Rectangle -7500403 true true 181 185 214 194
Circle -16777216 true false 144 174 42
Circle -16777216 true false 24 174 42
Circle -7500403 false true 24 174 42
Circle -7500403 false true 144 174 42
Circle -7500403 false true 234 174 42

turtle
true
0
Polygon -10899396 true false 215 204 240 233 246 254 228 266 215 252 193 210
Polygon -10899396 true false 195 90 225 75 245 75 260 89 269 108 261 124 240 105 225 105 210 105
Polygon -10899396 true false 105 90 75 75 55 75 40 89 31 108 39 124 60 105 75 105 90 105
Polygon -10899396 true false 132 85 134 64 107 51 108 17 150 2 192 18 192 52 169 65 172 87
Polygon -10899396 true false 85 204 60 233 54 254 72 266 85 252 107 210
Polygon -7500403 true true 119 75 179 75 209 101 224 135 220 225 175 261 128 261 81 224 74 135 88 99

wheel
false
0
Circle -7500403 true true 3 3 294
Circle -16777216 true false 30 30 240
Line -7500403 true 150 285 150 15
Line -7500403 true 15 150 285 150
Circle -7500403 true true 120 120 60
Line -7500403 true 216 40 79 269
Line -7500403 true 40 84 269 221
Line -7500403 true 40 216 269 79
Line -7500403 true 84 40 221 269

x
false
0
Polygon -7500403 true true 270 75 225 30 30 225 75 270
Polygon -7500403 true true 30 75 75 30 270 225 225 270
@#$#@#$#@
NetLogo 6.2.0
@#$#@#$#@
setup
repeat 180 [ go ]
@#$#@#$#@
@#$#@#$#@
<experiments>
  <experiment name="BoundaryTest" repetitions="60" sequentialRunOrder="false" runMetricsEveryStep="false">
    <setup>setup</setup>
    <go>go</go>
    <final>print ( word behaviorspace-run-number " done " )</final>
    <exitCondition>ticks &gt; 5 * (max-pxcor + 1) * (2 * max-pycor + 1) * 3.6 / speed-limit</exitCondition>
    <metric>ticks</metric>
    <metric>sum-visited / ticks / num-searchers</metric>
    <metric>sum-birdable / ticks / num-searchers</metric>
    <enumeratedValueSet variable="reflect-bias">
      <value value="0.1"/>
      <value value="0.2"/>
      <value value="0.3"/>
      <value value="0.4"/>
      <value value="0.5"/>
      <value value="0.6"/>
      <value value="0.7"/>
      <value value="0.8"/>
      <value value="0.9"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="num-resources">
      <value value="200"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="num-searchers">
      <value value="40"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="searcher-speed">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="search-turn-sd">
      <value value="2"/>
      <value value="3"/>
      <value value="4"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="ambient-level">
      <value value="30"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="base-percept">
      <value value="50"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="human-mult">
      <value value="4"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="noise-affects-resources?">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="num-vehicles">
      <value value="5"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="speed-limit">
      <value value="30"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="speed-limit-SD">
      <value value="0.2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="acceleration">
      <value value="0.05"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="excess-brake">
      <value value="5"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="vpass-probability">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="height-noiz">
      <value value="0.5"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="height-rcvr">
      <value value="1.6"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="temp-celsius">
      <value value="20"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="atm-pressure-bar">
      <value value="101"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="relative-humidity">
      <value value="60"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="ground-hardness">
      <value value="0.5"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="calc-noise">
      <value value="false"/>
    </enumeratedValueSet>
  </experiment>
  <experiment name="Paper2a" repetitions="5" sequentialRunOrder="false" runMetricsEveryStep="false">
    <setup>setup</setup>
    <go>go</go>
    <exitCondition>ticks &gt; 5 * (max-pxcor + 1) * (2 * max-pycor + 1) * 3.6 / speed-limit</exitCondition>
    <metric>ticks</metric>
    <metric>mean [ count resources-visited ] of searchers</metric>
    <metric>sqrt variance [ count resources-visited ] of searchers</metric>
    <metric>mean [ count resources-nonoise - count resources-visited ] of searchers</metric>
    <metric>mean ( unnest ( [ sound-history ] of searchers ) )</metric>
    <metric>mean ( unnest ( [ resourceNoise ] of searchers ) )</metric>
    <metric>mean ( unnest ( [ birderNoise ] of searchers ) )</metric>
    <metric>sqrt variance ( unnest ( [ sound-history ] of searchers ) )</metric>
    <metric>sqrt variance ( unnest ( [ resourceNoise ] of searchers ) )</metric>
    <metric>sqrt variance ( unnest ( [ birderNoise ] of searchers ) )</metric>
    <metric>mean ( unnest ( [ birdable-durations ] of searchers ) )</metric>
    <metric>mean ( unnest ( [ birdable-durationsNN ] of searchers ) )</metric>
    <metric>mean ( unnest ( [ birdable-absences ] of searchers ) )</metric>
    <metric>mean ( unnest ( [ birdable-absencesNN ] of searchers ) )</metric>
    <metric>mean ( unnest ( [ birderX ] of searchers ) )</metric>
    <metric>sqrt variance ( unnest ( [ birdable-durations ] of searchers ) )</metric>
    <metric>sqrt variance ( unnest ( [ birdable-durationsNN ] of searchers ) )</metric>
    <metric>sqrt variance ( unnest ( [ birdable-absences ] of searchers ) )</metric>
    <metric>sqrt variance ( unnest ( [ birdable-absencesNN ] of searchers ) )</metric>
    <metric>map [ ss -&gt; precision ( mean [ map [ x -&gt; x - ambient-level ] sound-history ] of ss ) 3 ] ( sort-on [ xcor ] stations )</metric>
    <metric>map [ ss -&gt; precision ( sqrt variance [ map [ x -&gt; x - ambient-level ] sound-history ] of ss ) 3 ] ( sort-on [ xcor ] stations )</metric>
    <metric>map [ x -&gt; ifelse-value [ sum absence-durations ] of x &gt; 0 [ [ precision ( sum-absent-noise / ( ticks - absent-tick + sum absence-durations )  ) 4 ] of x ] [ -1 ] ] ( sort-on [ xcor ] stations )map [ x -&gt; [ count searchers-detected ] of x ] ( sort-on [ xcor ] stations )</metric>
    <metric>map [ x -&gt; [ count searchers-detected ] of x ] ( sort-on [ xcor ] stations )</metric>
    <metric>map [ x -&gt; [ count searchers-detectedNN - count searchers-detected ] of x ] ( sort-on [ xcor ] stations )</metric>
    <metric>map [ x -&gt; ifelse-value length [ detection-durations ] of x &gt; 0 [ precision [ mean detection-durations / mean detection-durationsNN ] of x 5 ] [ ( -1 ) ] ] ( sort-on [ xcor ] stations )</metric>
    <metric>map [ x -&gt; ifelse-value length [ absence-durations ] of x &gt; 0 [ precision [ mean absence-durations / mean absence-durationsNN ] of x 5 ] [ ( -1 ) ] ] ( sort-on [ xcor ] stations )</metric>
    <metric>Veh-per-hour</metric>
    <metric>vph-unblocked</metric>
    <metric>Sum-visited</metric>
    <metric>Sum-birdable</metric>
    <metric>pxcor-replicates sort unnest [ sort resources-visited ] of searchers</metric>
    <metric>patches with [ hab = "resource" ]</metric>
    <enumeratedValueSet variable="reflect-bias">
      <value value="0.3"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="meters-moved-per-resource">
      <value value="50"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="num-searchers">
      <value value="40"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="searcher-speed">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="search-turn-sd">
      <value value="3"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="ambient-level">
      <value value="25"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="base-percept">
      <value value="50"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="human-mult">
      <value value="4"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="veh-name">
      <value value="&quot;sedan&quot;"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="noise-affects-resources?">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="num-vehicles">
      <value value="5"/>
      <value value="50"/>
      <value value="500"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="speed-limit">
      <value value="40"/>
      <value value="60"/>
      <value value="100"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="speed-limit-SD">
      <value value="0.2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="acceleration">
      <value value="0.05"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="excess-brake">
      <value value="5"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="vpass-probability">
      <value value="0.1"/>
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="height-noiz">
      <value value="0.5"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="height-rcvr">
      <value value="1.6"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="temp-celsius">
      <value value="20"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="atm-pressure-bar">
      <value value="101"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="relative-humidity">
      <value value="60"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="ground-hardness">
      <value value="0.5"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="calc-noise">
      <value value="true"/>
    </enumeratedValueSet>
  </experiment>
  <experiment name="Paper2b" repetitions="5" sequentialRunOrder="false" runMetricsEveryStep="false">
    <setup>setup</setup>
    <go>go</go>
    <exitCondition>ticks &gt; 5 * (max-pxcor + 1) * (2 * max-pycor + 1) * 3.6 / speed-limit</exitCondition>
    <metric>ticks</metric>
    <metric>mean [ count resources-visited ] of searchers</metric>
    <metric>sqrt variance [ count resources-visited ] of searchers</metric>
    <metric>mean [ count resources-nonoise - count resources-visited ] of searchers</metric>
    <metric>mean ( unnest ( [ sound-history ] of searchers ) )</metric>
    <metric>mean ( unnest ( [ resourceNoise ] of searchers ) )</metric>
    <metric>mean ( unnest ( [ birderNoise ] of searchers ) )</metric>
    <metric>sqrt variance ( unnest ( [ sound-history ] of searchers ) )</metric>
    <metric>sqrt variance ( unnest ( [ resourceNoise ] of searchers ) )</metric>
    <metric>sqrt variance ( unnest ( [ birderNoise ] of searchers ) )</metric>
    <metric>mean ( unnest ( [ birdable-durations ] of searchers ) )</metric>
    <metric>mean ( unnest ( [ birdable-durationsNN ] of searchers ) )</metric>
    <metric>mean ( unnest ( [ birdable-absences ] of searchers ) )</metric>
    <metric>mean ( unnest ( [ birdable-absencesNN ] of searchers ) )</metric>
    <metric>mean ( unnest ( [ birderX ] of searchers ) )</metric>
    <metric>sqrt variance ( unnest ( [ birdable-durations ] of searchers ) )</metric>
    <metric>sqrt variance ( unnest ( [ birdable-durationsNN ] of searchers ) )</metric>
    <metric>sqrt variance ( unnest ( [ birdable-absences ] of searchers ) )</metric>
    <metric>sqrt variance ( unnest ( [ birdable-absencesNN ] of searchers ) )</metric>
    <metric>map [ ss -&gt; precision ( mean [ map [ x -&gt; x - ambient-level ] sound-history ] of ss ) 3 ] ( sort-on [ xcor ] stations )</metric>
    <metric>map [ ss -&gt; precision ( sqrt variance [ map [ x -&gt; x - ambient-level ] sound-history ] of ss ) 3 ] ( sort-on [ xcor ] stations )</metric>
    <metric>map [ x -&gt; ifelse-value [ sum absence-durations ] of x &gt; 0 [ [ precision ( sum-absent-noise / ( ticks - absent-tick + sum absence-durations )  ) 4 ] of x ] [ -1 ] ] ( sort-on [ xcor ] stations )map [ x -&gt; [ count searchers-detected ] of x ] ( sort-on [ xcor ] stations )</metric>
    <metric>map [ x -&gt; [ count searchers-detected ] of x ] ( sort-on [ xcor ] stations )</metric>
    <metric>map [ x -&gt; [ count searchers-detectedNN - count searchers-detected ] of x ] ( sort-on [ xcor ] stations )</metric>
    <metric>map [ x -&gt; ifelse-value length [ detection-durations ] of x &gt; 0 [ precision [ mean detection-durations / mean detection-durationsNN ] of x 5 ] [ ( -1 ) ] ] ( sort-on [ xcor ] stations )</metric>
    <metric>map [ x -&gt; ifelse-value length [ absence-durations ] of x &gt; 0 [ precision [ mean absence-durations / mean absence-durationsNN ] of x 5 ] [ ( -1 ) ] ] ( sort-on [ xcor ] stations )</metric>
    <metric>Veh-per-hour</metric>
    <metric>vph-unblocked</metric>
    <metric>Sum-visited</metric>
    <metric>Sum-birdable</metric>
    <metric>pxcor-replicates sort unnest [ sort resources-visited ] of searchers</metric>
    <metric>patches with [ hab = "resource" ]</metric>
    <enumeratedValueSet variable="reflect-bias">
      <value value="0.3"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="meters-moved-per-resource">
      <value value="50"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="num-searchers">
      <value value="40"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="searcher-speed">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="search-turn-sd">
      <value value="3"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="ambient-level">
      <value value="30"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="base-percept">
      <value value="28.117066259517454"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="human-mult">
      <value value="4"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="veh-name">
      <value value="&quot;sedan&quot;"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="noise-affects-resources?">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="num-vehicles">
      <value value="5"/>
      <value value="50"/>
      <value value="500"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="speed-limit">
      <value value="40"/>
      <value value="60"/>
      <value value="100"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="speed-limit-SD">
      <value value="0.2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="acceleration">
      <value value="0.05"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="excess-brake">
      <value value="5"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="vpass-probability">
      <value value="0.1"/>
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="height-noiz">
      <value value="0.5"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="height-rcvr">
      <value value="1.6"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="temp-celsius">
      <value value="20"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="atm-pressure-bar">
      <value value="101"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="relative-humidity">
      <value value="60"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="ground-hardness">
      <value value="0.5"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="calc-noise">
      <value value="true"/>
    </enumeratedValueSet>
  </experiment>
  <experiment name="Paper2c" repetitions="5" sequentialRunOrder="false" runMetricsEveryStep="false">
    <setup>setup</setup>
    <go>go</go>
    <exitCondition>ticks &gt; 5 * (max-pxcor + 1) * (2 * max-pycor + 1) * 3.6 / speed-limit</exitCondition>
    <metric>ticks</metric>
    <metric>mean [ count resources-visited ] of searchers</metric>
    <metric>sqrt variance [ count resources-visited ] of searchers</metric>
    <metric>mean [ count resources-nonoise - count resources-visited ] of searchers</metric>
    <metric>mean ( unnest ( [ sound-history ] of searchers ) )</metric>
    <metric>mean ( unnest ( [ resourceNoise ] of searchers ) )</metric>
    <metric>mean ( unnest ( [ birderNoise ] of searchers ) )</metric>
    <metric>sqrt variance ( unnest ( [ sound-history ] of searchers ) )</metric>
    <metric>sqrt variance ( unnest ( [ resourceNoise ] of searchers ) )</metric>
    <metric>sqrt variance ( unnest ( [ birderNoise ] of searchers ) )</metric>
    <metric>mean ( unnest ( [ birdable-durations ] of searchers ) )</metric>
    <metric>mean ( unnest ( [ birdable-durationsNN ] of searchers ) )</metric>
    <metric>mean ( unnest ( [ birdable-absences ] of searchers ) )</metric>
    <metric>mean ( unnest ( [ birdable-absencesNN ] of searchers ) )</metric>
    <metric>mean ( unnest ( [ birderX ] of searchers ) )</metric>
    <metric>sqrt variance ( unnest ( [ birdable-durations ] of searchers ) )</metric>
    <metric>sqrt variance ( unnest ( [ birdable-durationsNN ] of searchers ) )</metric>
    <metric>sqrt variance ( unnest ( [ birdable-absences ] of searchers ) )</metric>
    <metric>sqrt variance ( unnest ( [ birdable-absencesNN ] of searchers ) )</metric>
    <metric>map [ ss -&gt; precision ( mean [ map [ x -&gt; x - ambient-level ] sound-history ] of ss ) 3 ] ( sort-on [ xcor ] stations )</metric>
    <metric>map [ ss -&gt; precision ( sqrt variance [ map [ x -&gt; x - ambient-level ] sound-history ] of ss ) 3 ] ( sort-on [ xcor ] stations )</metric>
    <metric>map [ x -&gt; ifelse-value [ sum absence-durations ] of x &gt; 0 [ [ precision ( sum-absent-noise / ( ticks - absent-tick + sum absence-durations )  ) 4 ] of x ] [ -1 ] ] ( sort-on [ xcor ] stations )map [ x -&gt; [ count searchers-detected ] of x ] ( sort-on [ xcor ] stations )</metric>
    <metric>map [ x -&gt; [ count searchers-detected ] of x ] ( sort-on [ xcor ] stations )</metric>
    <metric>map [ x -&gt; [ count searchers-detectedNN - count searchers-detected ] of x ] ( sort-on [ xcor ] stations )</metric>
    <metric>map [ x -&gt; ifelse-value length [ detection-durations ] of x &gt; 0 [ precision [ mean detection-durations / mean detection-durationsNN ] of x 5 ] [ ( -1 ) ] ] ( sort-on [ xcor ] stations )</metric>
    <metric>map [ x -&gt; ifelse-value length [ absence-durations ] of x &gt; 0 [ precision [ mean absence-durations / mean absence-durationsNN ] of x 5 ] [ ( -1 ) ] ] ( sort-on [ xcor ] stations )</metric>
    <metric>Veh-per-hour</metric>
    <metric>vph-unblocked</metric>
    <metric>Sum-visited</metric>
    <metric>Sum-birdable</metric>
    <metric>pxcor-replicates sort unnest [ sort resources-visited ] of searchers</metric>
    <metric>patches with [ hab = "resource" ]</metric>
    <enumeratedValueSet variable="reflect-bias">
      <value value="0.3"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="meters-moved-per-resource">
      <value value="50"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="num-searchers">
      <value value="40"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="searcher-speed">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="search-turn-sd">
      <value value="3"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="ambient-level">
      <value value="35"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="base-percept">
      <value value="15.811388300841896"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="human-mult">
      <value value="4"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="veh-name">
      <value value="&quot;sedan&quot;"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="noise-affects-resources?">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="num-vehicles">
      <value value="5"/>
      <value value="50"/>
      <value value="500"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="speed-limit">
      <value value="40"/>
      <value value="60"/>
      <value value="100"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="speed-limit-SD">
      <value value="0.2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="acceleration">
      <value value="0.05"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="excess-brake">
      <value value="5"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="vpass-probability">
      <value value="0.1"/>
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="height-noiz">
      <value value="0.5"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="height-rcvr">
      <value value="1.6"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="temp-celsius">
      <value value="20"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="atm-pressure-bar">
      <value value="101"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="relative-humidity">
      <value value="60"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="ground-hardness">
      <value value="0.5"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="calc-noise">
      <value value="true"/>
    </enumeratedValueSet>
  </experiment>
</experiments>
@#$#@#$#@
@#$#@#$#@
default
0.0
-0.2 0 0.0 1.0
0.0 1 1.0 0.0
0.2 0 0.0 1.0
link direction
true
0
Line -7500403 true 150 150 90 180
Line -7500403 true 150 150 210 180
@#$#@#$#@
1
@#$#@#$#@
