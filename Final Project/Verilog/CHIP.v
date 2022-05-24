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

    // Submodule
    imm_generator u_imm_generator(inst, imm_o);
    ALU u_ALU(in1, in2, alu_inst, alu_result, zero);
    ALU_control u_ALUcontrol(inst, alu_op, alu_inst, mul_valid);
    Control u_Control(inst, branch, mem_read, mem_to_reg, alu_op, mem_write, alu_src, reg_write);
    reg_file u_regfile(clk, rst_n, wen, a1, a2, aw, d, q1, q2);
    mulDiv u_mulDiv(clk, rst_n, valid, ready, mode, in_A, in_B, out);
endmodule

// CPU Architecture
module imm_generator(inst, imm_o);
    input [31:0] inst;
    output reg[31:0] imm_o;
    always @(inst) begin
        case(inst[6:0])
            // lui, auipc
            7'b0110111: imm_o = {inst[31:12], {12{1'b0}}};
            // jal
            7'b1101111: imm_o = {{11{inst[31]}}, inst[31], inst[19:12], inst[20], inst[30:21], 1'b0};
            // jalr
            7'b1100111: imm_o = {{20{inst[31]}}, inst[31:20]};
            // branch instruction: beq, bne, blt, bge, bltu, bgeu
            7'b1100011: imm_o = {{19{inst[31]}}, inst[31], inst[7], inst[30:25], inst[11:8], 1'b0};
            // Load instruction: lb, lh, lw, lbu, lhu 
            7'b0000011: imm_o = {{20{inst[31]}}, inst[31:20]};
            // Store instruction: sb sh, sw
            7'b0100011: imm_o = {{20{inst[31]}}, inst[31:25], inst[11:7]}; 
            // Logical gates: addi, slti, sltiu, xori, ori, andi
            7'b0010011: imm_o = {{20{inst[31]}}, inst[31:20]};
            // slli, srli, srai (shampt, 0~31)
            7'b0010011: imm_o = {27'b0, inst[24:20]};
            default: imm_o = {32{1'b0}};
        endcase
    end
endmodule

module ALU(in1, in2, alu_inst, alu_result, zero);
    input [31:0] in1, in2;
    input [10:0] alu_inst;
    output [31:0] alu_result;
    output reg zero;
    reg [31:0] result;
    assign alu_result = result;
    assign zero = (result == 32'b0) ? 1'b1 : 1'b0;
    // parameters for alu_inst from ALU_Control Unit (f7[5] + f3 + opc)
    parameter LUI   = 12'b00_000_0110111;
    parameter AUIPC = 12'b00_000_0010111;
    parameter JAL   = 12'b00_000_1101111;
    parameter JALR  = 12'b00_000_1100111;
    parameter ADDI  = 12'b00_000_0010011;
    parameter ADD   = 12'b00_000_0110011;
    parameter SUB   = 12'b10_000_0110011;
    parameter SLTI  = 12'b00_010_0010011;
    parameter SRLI  = 12'b00_101_0010011;
    parameter SLLI  = 12'b00_001_0010011;
    parameter BEQ   = 12'b00_000_1100011;
    parameter BNE   = 12'b00_001_1100011;
    parameter BLT   = 12'b00_100_1100011;
    parameter BGE   = 12'b00_101_1100011;

    always @(in1 or in2 or alu_inst) begin
        case(alu_inst)
            // lui
            LUI:  result = {in1[31:12], 12'b0};
            // auipc
            AUIPC:result = {in1[31:12], 12'b0} + in2;
            // jal (將 rd 設為pc 的值設為原本的 pc+4，然後將 pc 的值設為 imm 的結果)
            JAL:  result = in1 + 2'd4;
            // jalr (將 rd 設為pc 的值設為原本的 pc+4，然後將 pc 的值設為 給定address內的結果) (rd設為x0則代表不儲存return時的下一個地址)
            JALR: result = in1 + 2'd4;
            // addi
            ADDI: result = in1 + in2;
            // add
            ADD: result = in1 + in2;
            SUB:  result = in1 - in2;
            SLTI: result = (in1 < in2) ? 1'b1 : 1'b0;
            SRLI: result = in1 >> in2;
            SLLI: result = in1 << in2;
            default: result = 32'b0;
        endcase
        case(alu_inst)
            // jal (將 rd 設為pc 的值設為原本的 pc+4，然後將 pc 的值設為 imm 的結果)
            JAL:  zero = 1'b1 ;
            // jalr (將 rd 設為pc 的值設為原本的 pc+4，然後將 pc 的值設為 給定address內的結果) (rd設為x0則代表不儲存return時的下一個地址)
            JALR: zero = 1'b1 ;
            // beq
            BEQ: zero = (in1 == in2) ? 1'b1 : 1'b0;
            // bne
            BNE: zero = (in1 != in2) ? 1'b1 : 1'b0;
            //blt
            BLT: zero = (in1 <  in2) ? 1'b1 : 1'b0;
            //bge
            BGE: zero = (in1 >= in2) ? 1'b1 : 1'b0;
            default: zero = 1'b0;
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
    // ** 這邊有些問題，之後可能要重設
    parameter R  = 2'b10; 
    parameter ISB = 2'b01; 
    parameter UJ = 2'b00; 
    
    // parameters for alu_op from Control Unit
    parameter LUI   = 12'b00_000_0110111;
    parameter AUIPC = 12'b00_000_0010111;
    parameter JAL   = 12'b00_000_1101111;
    parameter JALR  = 12'b00_000_1100111;
    parameter ADDI  = 12'b00_000_0010011;
    parameter ADD   = 12'b00_000_0110011;
    parameter SUB   = 12'b10_000_0110011;
    parameter SLTI  = 12'b00_010_0010011;
    parameter SRLI  = 12'b00_101_0010011;
    parameter SLLI  = 12'b00_001_0010011;
    parameter BEQ   = 12'b00_000_1100011;
    parameter BNE   = 12'b00_001_1100011;
    parameter BLT   = 12'b00_100_1100011;
    parameter BGE   = 12'b00_101_1100011;

    always @(*) begin
        case(alu_op)
            ISB: alu = {2'b0, inst[14:12], inst[6:0]};
            R:   alu = {inst[30],inst[25], inst[14:12], inst[6:0]};
            UJ:  alu = {5'b0, inst[6:0]}
            default: alu = 12'b0000;
        endcase
        if (alu_op == R && inst[31:25] == 7'b0000001) mul_valid = 1'b1;
        else mul_valid = 1'b0;
    end
endmodule

module Control(inst, branch, mem_read, mem_to_reg, alu_op, mem_write, alu_src, reg_write);
    // output 可能不只圖上那些，要支援多一點功能要改這裡成比較大的control
    input [6:0] inst;
    output reg branch, mem_read, mem_to_reg, mem_write, alu_src, reg_write;
    output [2:0] alu_op;
    // parameters for alu_op 
    // ** 這邊有些問題，之後可能要重設
    parameter R  = 2'b10; 
    parameter ISB = 2'b01; 
    parameter UJ = 2'b10; 
    // parameter for inst
    parameter LUI =   6'b0110111;
    parameter AUIPC = 6'b0010111;
    parameter JAL   = 6'b1101111;
    parameter JALR  = 6'b1100111;
    parameter BBB   = 6'b1100011;
    parameter LLL   = 6'b0000011;
    parameter SSS   = 6'b0100011;
    parameter IMM   = 6'b0010011;
    parameter LOGIC = 6'b0110011;
    // 還未加入 alu_op
    always @(*) begin
        case(inst):
            // I
            LUI: begin
                branch = 1'b0;
                mem_read = 1'b1;
                mem_to_reg = 1'b1; 
                mem_write = 1'b0; 
                alu_src = 1'b1;
                reg_write = 1'b1;
            end
            // I
            AUIPC: begin
                branch = 1'b0;
                mem_read = 1'b1;
                mem_to_reg = 1'b1; 
                mem_write = 1'b0; 
                alu_src = 1'b1;
                reg_write = 1'b1;
            end
            // J
            JAL: begin
                branch = 1'b1;
                mem_read = 1'b0;
                mem_to_reg = 1'b0; 
                mem_write = 1'b0; 
                alu_src = 1'b1;
                reg_write = 1'b1;
            end
            // I
            JALR: begin
                branch = 1'b1;
                mem_read = 1'b0;
                mem_to_reg = 1'b0; 
                mem_write = 1'b0; 
                alu_src = 1'b0;
                reg_write = 1'b1;
            end
            // B
            BBB: begin
                branch = 1'b1;
                mem_read = 1'b0;
                mem_to_reg = 1'b0; 
                mem_write = 1'b0; 
                alu_src = 1'b0;
                reg_write = 1'b0;
            end
            // I
            LLL: begin
                branch = 1'b0;
                mem_read = 1'b1;
                mem_to_reg = 1'b1; 
                mem_write = 1'b0; 
                alu_src = 1'b1;
                reg_write = 1'b1;
            end
            SSS: begin
                branch = 1'b0;
                mem_read = 1'b0;
                mem_to_reg = 1'b0; 
                mem_write = 1'b1; 
                alu_src = 1'b1;
                reg_write = 1'b0;
            end
            IMM: begin
                branch = 1'b0;
                mem_read = 1'b0;
                mem_to_reg = 1'b0; 
                mem_write = 1'b0; 
                alu_src = 1'b1;
                reg_write = 1'b1;
            end
            LOGIC: begin
                branch = 1'b0;
                mem_read = 1'b0;
                mem_to_reg = 1'b0; 
                mem_write = 1'b0; 
                alu_src = 1'b0;
                reg_write = 1'b1;
            end
            default: begin
                branch = 1'b0;
                mem_read = 1'b0;
                mem_to_reg = 1'b0; 
                mem_write = 1'b0; 
                alu_src = 1'b0;
                reg_write = 1'b0;
            end
        endcase
    end
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
