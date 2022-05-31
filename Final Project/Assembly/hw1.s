
  
.data
    n: .word 11
.text
.globl __start

FUNCTION:
    # Todo: Define your own function in HW1
    addi sp, sp, -8
    sw x1, 4(sp)
    sw a0, 0(sp)
    beq x9, x0, init

    # if n >= 10
    addi x5, x0, 10
    bge x9, x5, Case1
    
    # else if 1 <= n < 10
    addi x5, x0, 1
    bge x9, x5, Case2
    
    # else if n = 0
    addi s1, x0, 7
    addi x10, s1, 0
    addi sp, sp, 8
    jalr x0, 0(x1)
    
init:
    addi x9, a0, 0
    jalr x0, 0(x1)

Case1:
    addi x6, x0, 3
    mul a0, x6, a0  
    srli a0, a0, 2 # n = 3/4n
    jal x1, FUNCTION
    addi x6, s1, 0
    
    lw x1, 4(sp)
    lw a0, 0(sp)
    addi x7, x0 ,2
    mul s1, x6, x7 # 2*T(3/4n)
    
    addi x7, x0, 7
    mul a0, a0, x7
    srli a0, a0, 3 # 7/8n
    add s1, s1, a0 # +7/8n
    
    addi s1, s1, -137 # -137
    addi sp, sp, 8
    jalr x0, 0(x1)
    
Case2:
    addi a0, a0, -1 # n = n - 1
    jal x1, FUNCTION
    addi x7, s1, 0
    
    lw x1, 4(sp)
    addi sp, sp, 8
    
    addi x6, x0, 2
    mul s1, x7, x6 # 2*T(n-1)
    jalr x0, 0(x1)

# Do NOT modify this part!!!
__start:
    la   t0, n
    lw   x10, 0(t0)
    jal  x1,FUNCTION
    la   t0, n
    sw   x10, 4(t0)
    addi a0,x0,10
    ecall
