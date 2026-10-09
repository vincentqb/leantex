cat <<MARKER
body MARK partial
MARKER
cat <<-'QUOTED'
	tab indented
	QUOTED
tr a-z A-Z <<\ESC
escaped
ESC
wc -l <<AB
ABC
AB
cat <<NEVER
NE only
echo done
