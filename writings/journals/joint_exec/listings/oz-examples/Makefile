

%.ozf: %.oz
	ozc -p -c $< -o $@

%.exe: %.oz
	ozc -p -x $< -o $@

test.exe: MyList.ozf

MyList.oz: Reverse.oz Member.oz Pairs.oz PPairs.oz
	echo "functor" > MyList.oz
	echo "import" >> MyList.oz
	echo "Search" >> MyList.oz
	echo "export" >> MyList.oz
	echo "Reverse" >> MyList.oz
	echo "Member" >> MyList.oz
	echo "Pair" >> MyList.oz
	echo "AllPairs" >> MyList.oz
	echo "define" >> MyList.oz
	cat Reverse.oz >> MyList.oz
	cat Member.oz >> MyList.oz
	cat Pairs.oz >> MyList.oz
	echo "end" >> MyList.oz

