(*  Title: 	FOCUS/ex/Coind.thy
    ID:         $ $
    Author: 	Franz Regensburger
    Copyright   1993 195 Technische Universitaet Muenchen

Example for co-induction on streams
*)

Coind = Stream + Dnat +


consts

	nats		:: "dnat stream"
	from		:: "dnat � dnat stream"

defs
	nats_def	"nats � fix`(�h.dzero&&(smap`dsucc`h))"

	from_def	"from � fix`(�h n.n&&(h`(dsucc`n)))"

end

(*
		smap`f`� = �
	x�� �� smap`f`(x&&xs) = (f`x)&&(smap`f`xs)

		nats = dzero&&(smap`dsucc`nats)

		from`n = n&&(from`(dsucc`n))
*)


