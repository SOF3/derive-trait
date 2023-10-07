README.md: src/lib.rs
	echo "# derive-trait" > $@
	grep -P '^//!' $^ | cut -c5- | sed 's/^#/##/' >> $@
