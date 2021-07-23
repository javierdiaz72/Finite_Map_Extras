build_options = -o document=pdf -g AFP -P :

properly:
	isabelle build $(build_options)

qnd:
	isabelle build -o quick_and_dirty $(build_options)
