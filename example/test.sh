randltl -n10 a b c --output=aut
a=0
while read line
do
    echo $a
    echo "File:$line"
    ltl2tgba --ba --unambiguous -f "$line" --output=ltlaut/aut$a.hoa
    seminator --complement=ncb ltlaut/aut$a.hoa
    autfilt ltlaut/aut$a.hoa --complement --output=true/tcom$a.hoa
    autfilt true/tcom$a.hoa --equivalent-to=com.hoa
    let a++
    echo -e "\n"
done <aut



