** jal (將 rd 設為pc 的值設為原本的 pc+4，然後將 pc 的值設為 imm 的結果)
** jalr (將 rd 設為pc 的值設為原本的 pc+4，然後將 pc 的值設為 給定address內的結果) (rd設為x0則代表不儲存return時的下一個地址)
** alu_op 的規則是如果opcode一定是相加則00, 若opcode一定相減則為01, 要看func3func7決定要幹嘛則為10
** alu_op 為00的可以共用alu
** Btype 便是一律相減的
** imm_gen很多沒加入忽略位，已改正，且已考慮全部可能性
** alu 還沒加入 mul
** alu_control還要再想一下在幹嘛(包括是否在這裡控制mul(in1,in2準備好了嗎??))
** control已考慮所有可能性，但有可能控制訊號有誤
** 還有一堆還沒做