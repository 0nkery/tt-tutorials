%language ElabReflection

triv : Elab ()
triv =
    do
        compute
        g <- getGoal
        case (snd g) of
            `(() : Type) =>
                do
                    fill `(() : ())
                    solve
            otherGoal =>
                fail [
                    TermPart otherGoal,
                    TextPart "is not trivial"
                ]

mkId : Elab ()
mkId =
    do
        intro `{{x}}
        fill (Var `{{x}})
        solve

idNat : Nat -> Nat
idNat = %runElab mkId

idUnit : () -> ()
idUnit = %runElab mkId

idString : String -> String
idString = %runElab mkId


