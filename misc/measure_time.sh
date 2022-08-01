#!/usr/bin/bash
# this script should be called from the root of the repository:
#  ./misc/measure_time.sh

fstar() {
fstar.exe \
	--include ./pure/ --include ./lowstar/ --include ./steel/ --include ./misc/ --include ./experiment/ \
	--include /home/ben/.switch/fstar/FStar/ulib/.cache \
	--include /home/ben/.switch/fstar/krml/krmllib \
	--include /home/ben/.switch/fstar/krml/krmllib/obj \
	--include ./obj \
	--already_cached 'Prims FStar LowStar C Spec.Loops TestLib WasmSupport Steel' \
	--warn_error '+241@247-274+285' --cache_dir obj --hint_dir hints \
	"$1"
}

for i in $(seq 1 20)
do
	echo
	sed -e 's/REPEAT/'$i'/g' < misc/MeasureTime.fst.template > misc/MeasureTime.fst
	{ fstar misc/MeasureTime.fst && rm misc/MeasureTime.fst ; } || { echo "error"; exit 1; }
done
