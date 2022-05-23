// Your code
module CHIP(clk,
            rst_n,
            // For mem_D
            mem_wen_D,
            mem_addr_D,
            mem_wdata_D,
            mem_rdata_D,
            // For mem_I
            mem_addr_I,
            mem_rdata_I);

    input         clk, rst_n ;
    // For mem_D
    output        mem_wen_D  ;
    output [31:0] mem_addr_D ;
    output [31:0] mem_wdata_D;
    input  [31:0] mem_rdata_D;
    // For mem_I
    output [31:0] mem_addr_I ;
    input  [31:0] mem_rdata_I;
    
    //---------------------------------------//
    // Do not modify this part!!!            //
    // Exception: You may change wire to reg //
    reg    [31:0] PC          ;              //
    wire   [31:0] PC_nxt      ;              //
    wire          regWrite    ;              //
    wire   [ 4:0] rs1, rs2, rd;              //
    wire   [31:0] rs1_data    ;              //
    wire   [31:0] rs2_data    ;              //
    wire   [31:0] rd_data     ;              //
    //---------------------------------------//

    // Todo: other wire/reg


    //---------------------------------------//
    // Do not modify this part!!!            //
    reg_file reg0(                           //
        .clk(clk),                           //
        .rst_n(rst_n),                       //
        .wen(regWrite),                      //
        .a1(rs1),                            //
        .a2(rs2),                            //
        .aw(rd),                             //
        .d(rd_data),                         //
        .q1(rs1_data),                       //
        .q2(rs2_data));                      //
    //---------------------------------------//

    // Todo: any combinational/sequential circuit
    // 做完CPU architecture的part後，在這組合成圖上的流程圖
    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            PC <= 32'h00010000; // Do not modify this value!!!
            
        end
        else begin
            PC <= PC_nxt;
            
        end
    end
endmodule


// CPU Architecture
module imm_generator(inst, imm_o);
    input [31:0] inst;
    output [31:0] imm_o;
    reg [31:0] imm;

    always @(inst) begin
        // branch instruction: beq, blt, bge, bltu, bgeu
        if (inst[6:0] == 7'b1100011)begin
            imm[12] = inst[31];
            imm[11] = inst[7];
            imm[10:5] = inst[30:25];
            imm[4:1] = inst[11:8];
            imm_o = {{20{imm[12]}}, imm[12:1]}; // make it 32-bit
        end

        // Load instruction: lb, lh, lw, lbu, lhu 
        // Logical gates: andi, ori, xori, 
        // Others: jalr, slti, sltiu
        else if (inst[6:0] == 7'b0000011 || inst[6:0] == 7'b0010011 || inst[6:0] == 7'b1100111) begin
            imm[11:0] = inst[31:20];
            imm_o = {{20{imm[11]}}, imm[11:0]};
        end

        // Store instruction: sb sh, sw
        else if (inst[6:0] == 7'b0100011) begin 
            imm[11:5] = inst[31:25];
            imm[4:0] = inst[11:7];
            imm_o = {{20{imm[11]}}, imm[11:0]}; 
        end

        // Others: lui, auipc
        else if (inst[6:0] == 7'b0110111 || inst[6:0] == 7'b0010111) begin
            imm[31:12] = inst[31:12];
            imm_o = {imm[31:12], {12{1'b0}}};
        end

        // 寫到這才發現用case可能比較NB.....我好爛==
        else imm_o = {32{1'b0}};
    end
endmodule

module adder(in1, in2, sum);
    input [31:0] in1;
    input [31:0] in2;
    output [31:0] sum;
    assign sum = in1 + in2;
endmodule

module andgate(in1, in2, out);
    input in1, in2;
    output out;
    assign out = in1 && in2;
endmodule

module mux32(in1, in2, sel, out);
    input [31:0] in1;
    input [31:0] in2;
    input sel;
    output [31:0] out;
    assign out = (!sel) ? in1 : in2;
endmodule

module shiftleft(in1, out);
    input [31:0] in1;
    output [31:0] out;
    assign out = {in1[30:0], 1'b0};
endmodule

module ALU(in1, in2, alu_inst, alu_result, zero);
    input [31:0] in1, in2;
    input [3:0] alu_inst;
    output [31:0] alu_result;
    output zero;
    reg [31:0] result;
    assign alu_result = result;
    assign zero = (result == 32'b0) ? 1'b1 : 1'b0;
    // parameters for alu_inst from ALU_Control Unit
    parameter BEQ4 = 4'b0000;
    parameter LWSW = 4'b0001;
    parameter ADDI = 4'b0010; // also for add
    parameter SLTI = 4'b0011;
    parameter SLLI = 4'b0100;
    parameter SRLI = 4'b0101;
    parameter SUB  = 4'b0110;
    parameter XOR  = 4'b0111;
    parameter MUL  = 4'b1000;

    always @(in1 or in2 or alu_inst) begin
        case(alu_inst)
            ADDI: result = in1 + in2;
            SUB: result = in1 - in2;
            SLTI: result = (in1 < in2) ? 1'b1 : 1'b0;
            SRLI: result = in1 >> in2;
            SLLI: result = in1 << in2;
            default: data_reg = 32'b0;
        endcase
    end
endmodule

module ALU_control(inst, alu_op, alu_inst, mul_valid);
    input [31:0] inst;
    input [2:0] alu_op;
    output [3:0] alu_inst;
    output mul_valid; // for the valid in mulDiv
    reg [3:0] alu;
    reg mul;
    assign alu_inst = alu;
    assign mul_valid = mul;

    // parameters for alu_op from Control Unit
    parameter BEQ = 3'b000; // beq
    parameter LS = 3'b001; // lw, sw
    parameter IMM_INST = 3'b010; // addi, slli, srli, slti (但我沒用srli在我的hw1的.s檔裡)
    parameter ARITHMETIC = 3'b011; // add, sub, mul
    parameter LOGIC = 3'b100; // xor, (and, or看你們要不要加，看起來是可以不用啦)
    
    // parameters for alu_inst
    parameter BEQ4 = 4'b0000;
    parameter LWSW = 4'b0001;
    parameter ADDI = 4'b0010; // also for add
    parameter SLTI = 4'b0011;
    parameter SLLI = 4'b0100;
    parameter SRLI = 4'b0101;
    parameter SUB  = 4'b0110;
    parameter XOR  = 4'b0111;
    parameter MUL  = 4'b1000;

    always @(*) begin
        case(alu_op) begin
            BEQ: alu = BEQ4;
            LS: alu = LWSW;
            IMM_INST: begin
                case(inst[14:12])
                    3'b000: alu = ADDI; // addi
                    3'b001: alu = SLTI; // slti
                    3'b010: alu = SLLI; // slli
                    3'b011: alu = SRLI; // srli
                    default: alu = 4'b0000;
                endcase
            end
            ARITHMETIC: begin
                case(inst[31:25])
                    7'b0000000: alu = ADDI; // add
                    7'b0000001: alu = MUL; // mul
                    7'b0100000: alu = SUB; // sub
                    default:alu = 4'b0000;
                endcase
            end
            LOGIC: alu = XOR;
            default: alu = 4'b0000;
        endcase
        if (alu_op == ARITHMETIC && inst[31:25] == 7'b0000001) mul_valid = 1'b1;
        else mul_valid = 1'b0;
    end

endmodule

module Control(inst, branch, mem_read, mem_to_reg, alu_op, mem_write, alu_src, reg_write);
    // output 可能不只圖上那些，要支援多一點功能要改這裡成比較大的control
    input [6:0] inst;
    output branch, mem_read, mem_to_reg, mem_write, alu_src, reg_write;
    output [2:0] alu_op;
    // parameters for alu_op 
    parameter BEQ = 3'b000; // beq
    parameter LS = 3'b001; // lw, sw
    parameter IMM_INST = 3'b010; // addi, slli, srli, slti (但我沒用srli在我的hw1的.s檔裡)
    parameter ARITHMETIC = 3'b011; // add, sub, mul
    parameter LOGIC = 3'b100; // xor, (and, or看你們要不要加，看起來是可以不用啦)

endmodule

module reg_file(clk, rst_n, wen, a1, a2, aw, d, q1, q2);

    parameter BITS = 32;
    parameter word_depth = 32;
    parameter addr_width = 5; // 2^addr_width >= word_depth

    input clk, rst_n, wen; // wen: 0:read | 1:write
    input [BITS-1:0] d;
    input [addr_width-1:0] a1, a2, aw;

    output [BITS-1:0] q1, q2;

    reg [BITS-1:0] mem [0:word_depth-1];
    reg [BITS-1:0] mem_nxt [0:word_depth-1];

    integer i;

    assign q1 = mem[a1];
    assign q2 = mem[a2];

    always @(*) begin
        for (i=0; i<word_depth; i=i+1)
            mem_nxt[i] = (wen && (aw == i)) ? d : mem[i];
    end

    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            mem[0] <= 0;
            for (i=1; i<word_depth; i=i+1) begin
                case(i)
                    32'd2: mem[i] <= 32'hbffffff0;
                    32'd3: mem[i] <= 32'h10008000;
                    default: mem[i] <= 32'h0;
                endcase
            end
        end
        else begin
            mem[0] <= 0;
            for (i=1; i<word_depth; i=i+1)
                mem[i] <= mem_nxt[i];
        end
    end
endmodule


// 這裡我只做mul，我看投影片似乎只要mul的功能，但它叫mulDiv，不知道要不要支援Div＠＠
module mulDiv(clk, rst_n, valid, ready, mode, in_A, in_B, out);
    // Todo: your HW2
    input         clk, rst_n;
    input         valid;
    input  [1:0]  mode; // mode: 0: mulu, 1: divu, 2: and, 3: avg
    output        ready;
    input  [31:0] in_A, in_B;
    output [31:0] out;

    // Definition of states
    parameter IDLE = 3'd0;
    parameter MUL  = 3'd1;
    parameter OUT  = 3'd2;

    // Todo: Wire and reg if needed
    reg  [ 2:0] state, state_nxt;
    reg  [ 4:0] counter, counter_nxt;
    reg  [63:0] shreg, shreg_nxt;
    reg  [31:0] alu_in, alu_in_nxt;
    reg  [32:0] alu_out;
    reg  [31:0] out;   // reg for output "out"
    reg  [ 0:0] ready; // reg for output "ready"

    always @(*) begin
        if (state == OUT) begin
            out = shreg[31:0];
            ready = 1;
        end 
        else begin
            out = 0;
            ready = 0;
        end
    end

    // Combinational always block
    // Todo 1: Next-state logic of state machine
    always @(*) begin
        case(state)
            IDLE: begin
                if (valid) state_nxt = MUL;
                else state_nxt = IDLE;
            end
            MUL: begin
                if(counter != 5'd31) state_nxt = MUL;
                else state_nxt = OUT;
            end
            default : state_nxt = IDLE;
        endcase
    end

    // Todo 2: Counter
    always @(*) begin
        if(state == MUL) counter_nxt = counter + 1;
        else counter_nxt = 0;
    end

    // ALU input
    always @(*) begin
        case(state)
            IDLE: begin
                if (valid) alu_in_nxt = in_B;
                else       alu_in_nxt = 0;
            end
            OUT : alu_in_nxt = 0;
            default: alu_in_nxt = alu_in;
        endcase
    end

    // Todo 3: ALU output
    always @(*) begin
        if (state == MUL) begin
            if (shreg[0] == 1'b1) alu_out = alu_in;
            else alu_out = 0;
        end
        else alu_out = 0;
    end

    // Todo 4: Shift register
    always @(*) begin
        case(state)
            IDLE: begin
                if (valid) shreg_nxt = {32'b0, in_A};
                else shreg_nxt = 0;
            end
            MUL: begin
                shreg_nxt = {shreg[63:32] + alu_out[31:0], shreg[31:0]} >> 1;
                if (shreg_nxt[62:31] < shreg[63:32]) shreg_nxt[63] = 1;
                else shreg_nxt[63] = 0;
            end
            default: shreg_nxt = 0;
        endcase
    end

    // Todo: Sequential always block
    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            state <= IDLE;
        end
        else begin
            state <= state_nxt;
            counter <= counter_nxt;
            shreg <= shreg_nxt;
            alu_in <= alu_in_nxt;
        end
    end

endmodule
