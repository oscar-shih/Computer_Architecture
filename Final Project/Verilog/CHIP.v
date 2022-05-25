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
    output [31:0] mem_addr_I ;//下個指令的位置
    input  [31:0] mem_rdata_I;//instuction的值
    
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
    //contol
    wire branch, mem_read, mem_to_reg,  mem_write, alu_src, reg_write;//control
    wire [1:0] alu_op;//alu_op 2 bits
    // alu input
    wire [31:0] in1,in2;

    wire [31:0] alu_result;
    wire [10:0] alu_inst;
    wire zero;
    
    //mul
    wire mul_valid,valid,mode,ready;
    wire [31:0]out;


    //---------------------------------------//
    // Do not modify this part!!!            //
    reg_file reg0(                           //
        .clk(clk),                           //
        .rst_n(rst_n),                       //
        .wen(reg_write),//有改               //
        .a1(rs1),                            //
        .a2(rs2),                            //
        .aw(rd),                             //
        .d(rd_data),                         //
        .q1(rs1_data),                       //
        .q2(rs2_data));                      //
    //---------------------------------------//
    assign  mem_addr_D  =   alu_result  ;
    assign  mem_wdata_D =   rs2_data    ;   

    // Todo: any combinational/sequential circuit
    
    // Submodule
    input_generator u_input_generator(.q1(rs1_data),.q2(rs2_data),.inst(mem_rdata_I),.alu_src(alu_src),
    .now_pc(PC), .in1(in1), .in2(in2));

    Control u_Control(.inst(mem_rdata_I), .branch(branch), .mem_read(mem_read), 
    .mem_to_reg(mem_to_reg), .alu_op(alu_op), .mem_write(mem_wen_D), .alu_src(alu_src), .reg_write(reg_write));

    ALU_control u_ALUcontrol( .inst(mem_rdata_I), .alu_op(alu_op), .alu_inst(alu_inst), .mul_valid(mul_valid));
    
    ALU u_ALU(.in1(in1), .im2(in2), .alu_inst(alu_inst), .alu_reslut(alu_result),.zero( zero));
    
    mulDiv u_mulDiv(clk, rst_n, valid, ready, mode, in_A, in_B, out);

    //-----------------------------------------------------------------------//
    //-----------------PC---------------//
    
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

//-------------------------------------------------------//
//從reg_file得出rs1,rs2得資料後，因應輸入instruction不同，有些rs1,rs2裡的資料事不能用的
//故使用這個input_generator 製作ALU所需要的兩個真正的輸入
module input_generator(
    input  [31:0] q1,
    input  [31:0] q2,
    input  [31:0] inst,
    input         alu_src,
    input  [31:0] now_pc,

    output [31:0] in1,
    output [31:0] in2
);
    wire    [31:0] imm_o;
    reg     [31:0] alu_data1,  alu_data2;
    imm_generator u_imm_generator(inst, imm_o);
    // parameters for alu_op from Control Unit
    parameter LUI   = 7'b0110111;
    parameter AUIPC = 7'b0010111;
    parameter JAL   = 7'b1101111;
    parameter JALR  = 7'b1100111;
    always @(*) begin
        case({inst[6:0]}):
            LUI:        alu_data1 = {imm_o[19:0],12'b0};
            AUIPC:      alu_data1 = {imm_o[19:0],12'b0};
            JAL:        alu_data1 = now_pc;
            JALR:       alu_data1 = now_pc;
            default:    alu_data1 = q1;
        endcase
        case({inst[6:0]}):
            LUI:        alu_data2 = 32'b0;
            AUIPC:      alu_data2 = now_pc;
            JAL:        alu_data2 = 32'd4;
            JALR:       alu_data2 = 32'd4;
            default:    alu_data2 = q2;
        endcase
    end
    assign in1 =  alu_data1;
    assign in2 = alu_src ? imm_o :  alu_data2;
endmodule


// 輸出imm_o
//---------------------------------------------------------------------------//
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

//------------------------------------------------------------------//
module ALU(in1, in2, alu_inst, alu_result, zero);
    input signed [31:0] in1, in2;
    input [10:0] alu_inst;
    output [31:0] alu_result;
    output reg zero;
    reg [31:0] result;
    assign alu_result = result;
    assign zero = (result == 32'b0) ? 1'b1 : 1'b0;
    // parameters for alu_inst from ALU_Control Unit (f7[5] + f3 + opc)
    parameter LS    = 12'b0; // jalr jal auipc lui ld sd
    parameter BEQ   = 12'b00_000_1100011; // sub
    parameter BNE   = 12'b00_001_1100011; // sub
    parameter BLT   = 12'b00_100_1100011; // sub
    parameter BGE   = 12'b00_101_1100011; // sub
    parameter ADDI  = 12'bxx_000_0010011; // func
    parameter ADD   = 12'b00_000_0110011; // func
    parameter SUB   = 12'b10_000_0110011; // func
    parameter SLTI  = 12'bxx_010_0010011; // func
    parameter SRLI  = 12'bxx_101_0010011; // func
    parameter SLLI  = 12'bxx_001_0010011; // func

    // jal (將 rd 設為pc 的值設為原本的 pc+4，然後將 pc 的值設為 imm 的結果)
    // jalr (將 rd 設為pc 的值設為原本的 pc+4，然後將 pc 的值設為 給定address內的結果) (rd設為x0則代表不儲存return時的下一個地址)
    always @(in1 or in2 or alu_inst) begin
        //result
        case(alu_inst)
            LS:   result = in1 + in2;
            // addi
            ADDI: result = in1 + in2;
            // beq
            BEQ:  result = in1 - in2;
            // bne
            BNE:  result = in1 - in2;
            //blt
            BLT:  result = in1 - in2;
            //bge
            BGE:  result = in1 - in2;
            // add
            ADD: result = in1 + in2;
            SUB:  result = in1 - in2;
            //
            SLTI: result = (in1 < in2) ? 1'b1 : 1'b0;
            SRLI: result = in1 >> in2;
            SLLI: result = in1 << in2;
            default: result = 32'b0;
        endcase
        //zero
        case(alu_inst)
            // beq
            BEQ: zero = (result == 32'b0) ? 1'b1 : 1'b0;
            // bne
            BNE: zero = (result != 32'b0) ? 1'b1 : 1'b0;
            //blt
            BLT: zero = (result[31] != 1'b0) ? 1'b1 : 1'b0;
            //bge
            BGE: zero = (result[31] == 1'b0) ? 1'b1 : 1'b0;
            default: zero = (result == 32'b0) ? 1'b1 : 1'b0;
        endcase
    end
endmodule

//---------------------------------------------------------------------//
module ALU_control(inst, alu_op, alu_inst, mul_valid);
    input [31:0] inst;
    input [1:0] alu_op;
    output [3:0] alu_inst;
    output mul_valid; // for the valid in mulDiv
    reg [3:0] alu;
    reg mul;
    assign alu_inst = alu;
    assign mul_valid = mul;

    // parameters for alu_op from Control Unit
    parameter RI  = 2'b10; 
    parameter B  = 2'b01; 
    parameter LS = 2'b00; 

    always @(*) begin
        case (alu_op):
            R: alu = {inst[30],inst[25], inst[14:12], inst[6:0]};
            B: alu = {2'b0, inst[14:12], inst[6:0]};
            LS: alu = 12'b0;

        endcase
        // 可能與I重複到，因此要檢查所有code
        if (inst[6:0] == 7'b0110011 && inst[31:25] == 7'b0000001) mul_valid = 1'b1;
        else mul_valid = 1'b0;
    end
endmodule

//----------------------------------------------------------------------------------------//
module Control(inst, branch, mem_read, mem_to_reg, alu_op, mem_write, alu_src, reg_write);
    // output 可能不只圖上那些，要支援多一點功能要改這裡成比較大的control
    input [6:0] inst;
    output reg branch, mem_read, mem_to_reg, mem_write, alu_src, reg_write;
    output [1:0] alu_op;
    // parameters for alu_op 
    parameter RI = 2'b10;   // look at funct
    parameter B  = 2'b01;   // Substract
    parameter LS = 2'b00;   // ADD
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
                alu_op = LS;
            end
            // I
            AUIPC: begin
                branch = 1'b0;
                mem_read = 1'b1;
                mem_to_reg = 1'b1; 
                mem_write = 1'b0; 
                alu_src = 1'b1;
                reg_write = 1'b1;
                alu_op = LS;
            end
            // J
            JAL: begin
                branch = 1'b1;
                mem_read = 1'b0;
                mem_to_reg = 1'b0; 
                mem_write = 1'b0; 
                alu_src = 1'b1;
                reg_write = 1'b1;
                alu_op = LS;
            end
            // I
            JALR: begin
                branch = 1'b1;
                mem_read = 1'b0;
                mem_to_reg = 1'b0; 
                mem_write = 1'b0; 
                alu_src = 1'b0;
                reg_write = 1'b1;
                alu_op = LS;
            end
            // B
            BBB: begin
                branch = 1'b1;
                mem_read = 1'b0;
                mem_to_reg = 1'b0; 
                mem_write = 1'b0; 
                alu_src = 1'b0;
                reg_write = 1'b0;
                alu_op = B;
            end
            // I
            LLL: begin
                branch = 1'b0;
                mem_read = 1'b1;
                mem_to_reg = 1'b1; 
                mem_write = 1'b0; 
                alu_src = 1'b1;
                reg_write = 1'b1;
                alu_op = LS;
            end
            SSS: begin
                branch = 1'b0;
                mem_read = 1'b0;
                mem_to_reg = 1'b0; 
                mem_write = 1'b1; 
                alu_src = 1'b1;
                reg_write = 1'b0;
                alu_op = LS;
            end
            IMM: begin
                branch = 1'b0;
                mem_read = 1'b0;
                mem_to_reg = 1'b0; 
                mem_write = 1'b0; 
                alu_src = 1'b1;
                reg_write = 1'b1;
                alu_op = RI;
            end
            LOGIC: begin
                branch = 1'b0;
                mem_read = 1'b0;
                mem_to_reg = 1'b0; 
                mem_write = 1'b0; 
                alu_src = 1'b0;
                reg_write = RI;
            end
            default: begin
                branch = 1'b0;
                mem_read = 1'b0;
                mem_to_reg = 1'b0; 
                mem_write = 1'b0; 
                alu_src = 1'b0;
                reg_write = 1'b0;
                reg_write = 2'b11;
            end
        endcase
    end
endmodule

//-----------------------------------------------------------//
module reg_file(clk, rst_n, wen, a1, a2, aw, d, q1, q2);

    parameter BITS = 32;
    parameter word_depth = 32;// 32 bits word
    parameter addr_width = 5; // 2^addr_width >= word_depth

    input clk, rst_n, wen; // wen=Regwrite:  0:read / 1:write
    input [BITS-1:0] d;
    input [addr_width-1:0] a1, a2, aw;//rs1,rs2,rd

    output [BITS-1:0] q1, q2;//data in rsi,rs2

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
