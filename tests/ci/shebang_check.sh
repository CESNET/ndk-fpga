#! /bin/sh
#
# Checks that Python scripts have a consistent shebang / executable-bit pairing:
# - a tracked file starting with a "#!.../python..." shebang must be executable
# - a tracked *.py file that is executable must start with a python shebang
# - any python shebang present must be the "#!/usr/bin/env python3" standard form
#
# A few filenames carry a fixed convention regardless of their content, and are
# checked against that convention instead of the generic rule above:
#   - ver_settings.py / synth_settings.py   - plain config files
#   - cocotb_test.py                        - cocotb entry module
#   - setup.py                              + setuptools entry point

failed=0
tmpfile=$(mktemp)
trap 'rm -f "$tmpfile"' EXIT

is_python_shebang() {
	case "$1" in
		"#!"*python*) return 0 ;;
		*) return 1 ;;
	esac
}

is_standard_python_shebang() {
	case "$1" in
		"#!/usr/bin/env python"[0-9]*) return 0 ;;
		*) return 1 ;;
	esac
}

check_shebang_form() {
	if [ "$has_shebang" -eq 1 ] && ! is_standard_python_shebang "$first_line"; then
		echo "FAIL(python): $f shebang '$first_line' should be '#!/usr/bin/env python3'"
		failed=1
	fi
}

check_python_file() {
	f="$1"

	# cheap probe before reading a full line, so binary files are not read as text
	first_line=""
	if [ "$(head -c 2 -- "$f" 2>/dev/null)" = "#!" ]; then
		first_line=$(head -n 1 -- "$f" 2>/dev/null)
	fi

	is_exec=0
	[ -x "$f" ] && is_exec=1

	has_shebang=0
	is_python_shebang "$first_line" && has_shebang=1

	base=$(basename -- "$f")

	case "$base" in
		ver_settings.py | synth_settings.py | cocotb_test.py)
			if [ "$has_shebang" -eq 1 ]; then
				echo "FAIL(python): $f is a '$base' file and must not have a shebang"
				failed=1
			fi
			if [ "$is_exec" -eq 1 ]; then
				echo "FAIL(python): $f is a '$base' file and must not be executable"
				failed=1
			fi
			return
			;;
		setup.py)
			if [ "$has_shebang" -eq 0 ]; then
				echo "FAIL(python): $f is a setup.py entry point and must start with a python shebang"
				failed=1
			fi
			if [ "$is_exec" -eq 0 ]; then
				echo "FAIL(python): $f is a setup.py entry point and must be executable (chmod +x)"
				failed=1
			fi
			check_shebang_form
			return
			;;
	esac

	if [ "$has_shebang" -eq 1 ] && [ "$is_exec" -eq 0 ]; then
		echo "FAIL(python): $f has a python shebang but is not executable (chmod +x)"
		failed=1
	fi

	if [ "$is_exec" -eq 1 ] && [ "$has_shebang" -eq 0 ]; then
		echo "FAIL(python): $f is executable but has no python shebang"
		failed=1
	fi

	check_shebang_form
}

check_python_files() {
	# scoped to *.py for speed
	git ls-files -- '*.py' > "$tmpfile"
	while IFS= read -r f; do
		check_python_file "$f"
	done < "$tmpfile"
}

check_python_files

if [ "$failed" -eq 1 ]; then
	echo
	echo "One or more python scripts have an inconsistent shebang / executable-bit pairing."
	echo "See tests/ci/shebang_check.sh for the rules."
	exit 1
fi
