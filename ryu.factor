! Copyright (C) 2018 Alexander Ilin.
! See http://factorcode.org/license.txt for BSD license.
USING: formatting kernel locals math math.bitwise math.order
ryu.data sequences strings vectors ;

IN: ryu

<PRIVATE

: mul-shift ( x mul shift -- y )
    [ first2 rot [ * ] keep swapd * -64 shift + ] [ 64 - neg ] bi* shift ;

: mul-shift-all ( mmShift m mul shift -- vm vp vr )
    [ [ 4 * 1 - swap - ] 2dip mul-shift ]
    [ [ 4 * 2 +        ] 2dip mul-shift ]
    [ [ 4 *            ] 2dip mul-shift ] 3tri ;

: multiple-of-5? ( value -- ? )
    5 rem zero? ;

:: pow-5-factor ( x -- y )
    0 :> count!
    0 :> result!
    x :> value!
    f :> finished!
    [ count x <= finished not and ] [
        value multiple-of-5? [
            value 5 /i value!
            count 1 + count!
        ] [
            t finished!
            count result!
        ] if
    ] while result ;

: multiple-of-power-of-5 ( value p -- ? )
    [ pow-5-factor ] dip >= ;

: double-pow-5-bits ( n -- m )
    dup 0 = [ drop 1 ] [
        DOUBLE_LOG2_5_NUMERATOR * DOUBLE_LOG2_5_DENOMINATOR + 1 -
        DOUBLE_LOG2_5_DENOMINATOR /i
    ] if ;

: decimal-length ( m -- n )
    {
        10
        100
        1000
        10000
        100000
        1000000
        10000000
        100000000
        1000000000
        10000000000
        100000000000
        1000000000000
        10000000000000
        100000000000000
        1000000000000000
        10000000000000000
        100000000000000000
        1000000000000000000
    } [ dupd >= ] find-last [ 2 + ] [ drop 1 ] if nip ;

CONSTANT: mantissaBits 52
CONSTANT: exponentBits 11
CONSTANT: offset 1023 ! (1 << (exponentBits - 1)) - 1

:: unpack-bits ( f debug? -- e2 m2 acceptBounds ieeeExponent<=1? neg? string/f )
    f double>bits
    dup mantissaBits exponentBits + bit? :> sign
    dup mantissaBits bits :> ieeeMantissa
    dup mantissaBits neg shift exponentBits bits :> ieeeExponent

    debug? [ dup "IN=%b\n" printf ] when
    drop

    0 :> m2!
    0 :> e2!
    exponentBits on-bits ieeeExponent = [
        ieeeMantissa zero? [ sign "-Inf" "Inf" ? ] [ "NaN" ] if
    ] [
        ieeeExponent zero? [
            ieeeMantissa zero? [ sign "-0.0" "0.0" ? ] [
                1 offset - mantissaBits - 2 - e2!
                ieeeMantissa m2!
                f
            ] if
        ] [
            ieeeExponent offset - mantissaBits - 2 - e2!
            ieeeMantissa mantissaBits set-bit m2!
            f
        ] if
    ] if

    debug? [ sign "-" "+" ? e2 2 + m2 "S=%s E=%x M=%x\n" printf ] when
    [ e2 m2 dup even? ieeeExponent 1 <= sign ] dip ;

: bool>str ( ? -- string )
    "true" "false" ? ;

PRIVATE>

:: print-float ( float debug? -- string )
    float >float debug? unpack-bits [
        [ 5drop ] dip
    ] [| e2 m2 acceptBounds ieeeExponent<=1 sign |
        25 <vector> :> result
        m2 4 * :> mv
        mantissaBits 2^ m2 = not ieeeExponent<=1 or 1 0 ? :> mmShift
        f :> vmIsTrailingZeros!
        f :> vrIsTrailingZeros!
        0 :> e10!
        0 :> vr!
        0 :> vp!
        0 :> vm!

        e2 0 >= [
            e2 DOUBLE_LOG10_2_NUMERATOR * DOUBLE_LOG10_2_DENOMINATOR /i 0 max :> q
            q e10!
            q double-pow-5-bits DOUBLE_POW5_INV_BITCOUNT * 1 - :> k
            q k + e2 - :> i
            mmShift m2 q DOUBLE_POW5_INV_SPLIT nth i mul-shift-all
            :> ( vm! vp! vr! )

            debug? [
                mv e2 q "%d * 2^%d / 10^%d\n" printf
                vp vr vm "V+=%d\nV =%d\nV-=%d\n" printf
            ] when

            q 21 <= [
                mv 5 rem zero? [
                    mv q multiple-of-power-of-5 :> vrIsTrailingZeros!
                ] [
                    acceptBounds [
                        mv mmShift - 1 - q multiple-of-power-of-5 vmIsTrailingZeros!
                    ] [
                        vp mv 2 + q multiple-of-power-of-5 - vp!
                    ] if
                ] if
            ] when
        ] [ ! e2 < 0
            e2 neg DOUBLE_LOG10_5_NUMERATOR * DOUBLE_LOG10_5_DENOMINATOR /i 1 - 0 max :> q
            q e2 + e10!
            e2 neg q - :> i
            i double-pow-5-bits DOUBLE_POW5_BITCOUNT - :> k
            q k - :> j
            mmShift m2 i DOUBLE_POW5_SPLIT nth j mul-shift-all
            :> ( vm! vp! vr! )

            debug? [
                mv e2 neg q "%d * 5^%d / 10^%d\n" printf
                q i k j "%d %d %d %d\n" printf
                vp vr vm "V+=%d\nV =%d\nV-=%d\n" printf
            ] when

            q 1 <= [
                mv 1 bitand bitnot q >= vrIsTrailingZeros!
                acceptBounds [
                    mv 1 - mmShift - bitnot 1 bitand q >= vmIsTrailingZeros!
                ] [ vp 1 - vp! ] if
            ] [
                q 63 < [
                    q 1 - 2^ 1 - mv bitand zero? vrIsTrailingZeros!
                    debug? [
                        vrIsTrailingZeros bool>str "vr is trailing zeros=%s\n" printf
                    ] when
                ] when
            ] if
        ] if

        debug? [
            e10 "e10=%d\n" printf
            vp vr vm "V+=%d\nV =%d\nV-=%d\n" printf
            vrIsTrailingZeros bool>str "vr is trailing zeros=%s\n" printf
            vmIsTrailingZeros bool>str "vm is trailing zeros=%s\n" printf
        ] when

        vp decimal-length :> vplength
        e10 vplength + 1 - :> exp!
        0 :> removed!
        0 :> lastRemovedDigit!
        0 :> output!
        vmIsTrailingZeros vrIsTrailingZeros or [
            ! rare
            [ vp 10 /i vm 10 /i > ] [
                vm 10 /i 10 * vm = vmIsTrailingZeros and vmIsTrailingZeros!
                lastRemovedDigit zero? vrIsTrailingZeros and vrIsTrailingZeros!
                vr 10 /i :> nvr
                vr nvr 10 * - lastRemovedDigit!
                nvr vr!
                vp 10 /i vp!
                vm 10 /i vm!
                removed 1 + removed!
            ] while

            debug? [ vp vr vm "V+=%d\nV =%d\nV-=%d\n" printf ] when

            vmIsTrailingZeros [
                [ vm 10 /i 10 * vm = ] [
                    lastRemovedDigit zero? vrIsTrailingZeros and vrIsTrailingZeros!
                    vr 10 /i :> nvr
                    vr nvr 10 * - lastRemovedDigit!
                    nvr vr!
                    vp 10 /i vp!
                    vm 10 /i vm!
                    removed 1 + removed!
                ] while
            ] when

            debug? [ vr lastRemovedDigit "%d %d\n" printf ] when

            vrIsTrailingZeros lastRemovedDigit 5 = and vr even? and [
                4 lastRemovedDigit!
            ] when
            acceptBounds vmIsTrailingZeros and not vr vm = and
            lastRemovedDigit 5 >= or 1 0 ? vr + output!
        ] [
            ! common
            [ vp 10 /i vm 10 /i > ] [
                vr 10 /i :> nvr
                vr nvr 10 * - lastRemovedDigit!
                nvr vr!
                vp 10 /i vp!
                vm 10 /i vm!
                removed 1 + removed!
            ] while

            debug? [ vr lastRemovedDigit "%d %d\n" printf ] when

            vr vm = lastRemovedDigit 5 >= or 1 0 ? vr + output!
        ] if
        vplength removed - :> olength

        debug? [
            vp vr vm "V+=%d\nV =%d\nV-=%d\n" printf
            output "O=%d\n" printf
            olength "OLEN=%d\n" printf
            exp "EXP=%d\n" printf
        ] when

        0 :> index!
        sign [ CHAR: - 0 result set-nth 1 index! ] when
        0 :> i!
        output :> output2!
        [ output2 10000 >= ] [
            output2 output2 10000 /i 10000 * - :> c
            output2 10000 /i output2!
            index olength + i - 1 - :> res-index
            c 100 rem 2 *
            dup DIGIT_TABLE nth res-index result set-nth
            1 + DIGIT_TABLE nth res-index 1 + result set-nth
            c 100 /i 2 *
            dup DIGIT_TABLE nth res-index 2 - result set-nth
            1 + DIGIT_TABLE nth res-index 1 - result set-nth
            i 4 + i!
        ] while
        output2 100 >= [
            output2 output2 100 /i 100 * - :> c
            output2 100 /i output2!
            index olength + i - :> res-index
            c DIGIT_TABLE nth res-index 1 - result set-nth
            c 1 + DIGIT_TABLE nth res-index result set-nth
            i 2 + i!
        ] when
        output2 10 >= [
            output2 2 * :> c
            index olength + i - :> res-index
            c 1 + DIGIT_TABLE nth res-index result set-nth
            c DIGIT_TABLE nth index result set-nth
        ] [ CHAR: 0 output2 + index result set-nth ] if
        olength 1 > [ CHAR: . index 1 + result set-nth ] [ index 1 + index! ] if
        CHAR: e index result set-nth
        index 1 + index!
        exp neg? [
            CHAR: - index result set-nth
            index 1 + index!
            exp neg exp!
        ] when
        exp 100 >= [
            CHAR: 0 exp 100 /i + index result set-nth
            index 1 + index!
            exp exp 100 /i 100 * - exp!
            exp 2 * DIGIT_TABLE nth index result set-nth
            exp 2 * 1 + DIGIT_TABLE nth index 1 + result set-nth
            index 2 + index!
        ] [
            exp 10 >= [
                exp 2 * DIGIT_TABLE nth index result set-nth
                exp 2 * 1 + DIGIT_TABLE nth index 1 + result set-nth
            ] [
                CHAR: 0 exp + index result set-nth
            ] if
        ] if

        result >string
    ] if* ;
