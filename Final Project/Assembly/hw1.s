
  
.data
    n: .word 11
.text
.globl __start

FUNCTION:
    # Todo: Define your own function in HW1
    addi sp, sp, -8
    sw x1, 4(sp)
    sw x28, 0(sp)

    # if n >= 10
    addi x5, x0, 10
    bge x28, x5, Case1
    
    # else if 1 <= n < 10
    addi x5, x0, 1
    bge x28, x5, Case2
    
    # else if n = 0
    addi a0, x0, 7
    addi x10, a0, 0
    addi sp, sp, 8
    jalr x0, 0(x1)


Case1:
    addi x6, x0, 3
    mul x28, x6, x28  
    srli x28, x28, 2 # n = 3/4n
    jal x1, FUNCTION
    addi x6, a0, 0
    
    lw x1, 4(sp)
    lw x28, 0(sp)
    addi x7, x0 ,2
    mul a0, x6, x7 # 2*T(3/4n)
    
    addi x7, x0, 7
    mul x28, x28, x7
    srli x28, x28, 3 # 7/8n
    add a0, a0, x28 # +7/8n
    
    addi a0, a0, -137 # -137
    addi sp, sp, 8
    jalr x0, 0(x1)
    
Case2:
    addi x28, x28, -1 # n = n - 1
    jal x1, FUNCTION
    addi x7, a0, 0
    
    lw x1, 4(sp)
    addi sp, sp, 8
    
    addi x6, x0, 2
    mul a0, x7, x6 # 2*T(n-1)
    jalr x0, 0(x1)

# Do NOT modify this part!!!
__start:
    la   t0, n
    lw   x28, 0(t0)
    jal  x1,FUNCTION
    la   t0, n
    sw   a0, 4(t0)
    addi a0,x0,10
    ecall
