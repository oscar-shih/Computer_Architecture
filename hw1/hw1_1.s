.globl __start

.rodata
    msg0: .string "This is HW1-1: \nT(n) = 2T(3n/4) + 0.875n - 137, n >= 10\n"
    msg1: .string "T(n) = 2T(n-1), 1 <= n < 10\nT(0) = 7\n"
    msg2: .string "Enter a number: "
    msg3: .string "The result is: "
.text

__start:
  # Prints msg0
    addi a0, x0, 4
    la a1, msg0
    ecall
  # Prints msg1
    addi a0, x0, 4
    la a1, msg1
    ecall
  # Prints msg2
    addi a0, x0, 4
    la a1, msg2
    ecall
  # Reads an int
    addi a0, x0, 5
    ecall
    
    jal Main
    jal result
    
################################################################################ 
  # Write your main function here. 
  # The input n is in a0. 
  # You should store the result T(n) into t0.
  # Round down the result of division.
  
  # HW1_1 
  # T(n) = 2T(3n/4) + 0.875n - 137, n >= 10
  # T(n) = 2T(n-1), 1 <= n < 10
  # T(0) = 7

  # EX. addi t0, a0, 1
################################################################################
Main:
    addi sp, sp, -8
    sw x1, 4(sp)
    sw a0, 0(sp)
    
    # if n >= 10
    addi x5, x0, 10
    bge a0, x5, Case1
    
    # else if 1 <= n < 10
    addi x5, x0, 1
    bge a0, x5, Case2
    
    # else if n = 0
    addi t0, x0, 7
    addi sp, sp, 8
    jalr x0, 0(x1)
    
Case1:
    addi x6, x0, 3
    mul a0, x6, a0  
    srli a0, a0, 2 # n = 3/4n
    jal x1, Main
    addi x6, t0, 0
    
    lw x1, 4(sp)
    lw a0, 0(sp)
    addi x7, x0 ,2
    mul t0, x6, x7 # 2*T(3/4n)
    
    addi x7, x0, 7
    mul a0, a0, x7
    srli a0, a0, 3 # 7/8n
    add t0, t0, a0 # +7/8n
    
    addi t0, t0, -137 # -137
    addi sp, sp, 8
    jalr x0, 0(x1)
    
Case2:
    addi a0, a0, -1 # n = n - 1
    jal x1, Main
    addi x7, t0, 0
    
    lw x1, 4(sp)
    addi sp, sp, 8
    
    addi x6, x0, 2
    mul t0, x7, x6 # 2*T(n-1)
    jalr x0, 0(x1)
    
result:
  # Prints msg3
    addi a0, x0, 4
    la a1, msg3
    ecall
  # Prints the result in t0
    addi a0, x0, 1
    add a1, x0, t0
    ecall
  # Ends the program with status code 0
    addi a0, x0, 10
    ecall    