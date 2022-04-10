.globl __start

.rodata
    msg0: .string "This is HW1_2: \n"
    msg1: .string "Plaintext: "
    msg2: .string "Ciphertext: "
.text

################################################################################
# print_char function
# Usage: 
#     1. Store the beginning address in x20
#     2. Use "j print_char"
#     The function will print the string stored from x20 
#     When finish, the whole program will return value 0
print_char:
    addi a0, x0, 4
    la a1, msg2
    ecall
    
    add a1, x0, x20
    ecall
# Ends the program with status code 0
    addi a0, x0, 10
    ecall
################################################################################
################################################################################
__start:
# Prints msg
    addi a0, x0, 4
    la a1, msg0
    ecall
    
    la a1, msg1
    ecall
    
    addi a0, x0, 8
    
    li a1, 0x10130
    addi a2, x0, 2047
    ecall
# Load address of the input string into a0
    add a0, x0, a1
################################################################################   
################################################################################ 
# Write your main function here. 
# a0 stores the beginning Plaintext
# Do store 66048(0x10200) into x20 
main:
    li x20, 0x10200   # store 66048(0x10200) into x20
    addi x21, x20, 0  
    addi x6, x0, 0x0a   #x6: "\n"
    addi x7, x0, 0      #x7:counter
    
while_loop:
    lb x5, 0(a0)      
    beq x5, x6, exit    
    
    addi x8, x0, 0x2c   
    beq x5, x8, L1      # if ","
    addi x8, x0, 0x61   
    bge x5, x8, L2      # if "a" ~ "z"
    jal x0, out
    
L1: # To count "," number  down from 9.                
    addi x5, x0, 0x39  # x5 = 9  
    sub x5, x5, x7     # x5 -= 1 if "," shows up
    addi x7, x7, 1
    jal x0, out
    
L2: # "a" ~ "m"
    addi x8, x0, 0x7a   # x8 = "z"
    bgt x5, x8, out   # if x5 > z 
    addi x8, x0, 0x6e   # x8 = "n"
    bge x5, x8, L3
    addi x5, x5, -19
    jal x0, out
    
L3: # "n" ~ "z"
    addi x5, x5, -45
    jal x0, out
    
out:            
    sb x5, 0(x21)
    addi a0, a0, 1
    addi x21, x21, 1
    jal x0, while_loop
    
exit:
    sb x6, 0(x21)
    j print_char
################################################################################    
