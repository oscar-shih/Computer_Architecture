***   la t0 n : 步驟為先load現在pc位置(auipc)，再將該pc位置加上與n存的位置的差距(addi)。
			以此code來說他是存在最後一個至另的後一個address，也就是此指令的36個address後。
			這部分要先在memory寫好n是多少
***   修改 main 為 FUNCTION
***   修改 t0 為 s1 : 由於t0是拿來存address來access memory，因此將t0改成沒用的s1(x9)。
				以確認測資正確