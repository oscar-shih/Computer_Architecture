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

assign rs1 = mem_rdata_I[19:15];
assign rs2 = mem_rdata_I[24:20];
assign rd = mem_rdata_I[11:7];

//control signal
wire branch;
wire mem_to_reg;
wire alu_src;
wire auipc;
wire jal;
wire jalr;
wire zero;
wire done;
wire mul_op;
wire [2:0]  alu_op;
wire [3:0]  alu_inst;
//imm
wire [31:0] imm,imm_ls1;
//alu
wire [31:0] alu_input_1,alu_input_2;
wire [31:0] alu_out,mul_out,alu_out_final;
//rd
wire [31:0] rd_jal;
//pc
wire [31:0] pc_4, pc_imm,pc_branch,pc_jump_rs,pc_jump;
//ALU OUTPUT
assign alu_out_final=mul_op?mul_out:alu_out;
//RD DATA
assign rd_jal=jal? pc_4:alu_out_final;
assign rd_data=mem_to_reg?mem_rdata_D:rd_jal;
//------------------------------------------------------
//PC
//
//BRANCH
assign imm_ls1=imm<<1;
assign pc_4=PC+32'd4;
assign pc_imm=PC+imm_ls1;
assign pc_branch= branch &zero?  pc_imm: pc_4;
//JAL JALR
assign pc_jump_rs=jalr? rs1_data:PC;
assign pc_jump=pc_jump_rs+imm;
assign PC_nxt= jal?pc_jump:pc_branch;
//---------------------------------------------
//OUTPUT
assign mem_addr_D = alu_out;
assign mem_wdata_D = rs2_data;
assign mem_addr_I = PC;
//-------------------------------------------

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
Control Control(
.opcode(mem_rdata_I[6:0]), 
.branch(branch),
.mem_write(mem_wen_D),
.mem_to_reg(mem_to_reg), 
.alu_op(alu_op), 
.alu_src(alu_src),
.auipc(auipc), 
.reg_write(regWrite),
.jal(jal),
.jalr(jalr)
);


ALU_Control ALU_Control(
.func7(mem_rdata_I[31:25]),
.func3(mem_rdata_I[14:12]),  
.alu_op(alu_op),
.alu_inst(alu_inst), 
.mul_op(mul_op)       
);

imm_gen imm_gen(
.inst(mem_rdata_I),
.imm_o(imm)
);

assign alu_input_2=alu_src? imm:rs2_data;
assign alu_input_1=auipc? PC :rs1_data;

ALU ALU(
.data_1(alu_input_1), 
.data_2(alu_input_2), 
.alu_inst(alu_inst), 
.data_out(alu_out), 
.zero(zero)
);

mul mul(
.clk(clk),
.rst_n(rst_n),
.valid(mul_op),
.in_A(alu_input_1),
.in_B(alu_input_2),
.done(done),
.mul_out(mul_out)
);

always @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
    PC <= 32'h00010000; // Do not modify this value!!!

    end
    else begin
    if (done) begin
        PC <= PC_nxt;
    end
    else begin
        PC <= PC;
    end

    end
    end
endmodule
//---------------------------------------------------------------------------
//SUNMODULE
module imm_gen(inst, imm_o);
    input  [31:0] inst;
    output reg [31:0] imm_o;
    localparam IMM  =   7'b0010011;
    localparam R    =   7'b0110011;
    localparam BEQ  =   7'b1100011;
    localparam LOAD =   7'b0000011;
    localparam STORE=   7'b0100011;
    localparam AUIPC=   7'b0010111;
    localparam JAL  =   7'b1101111;
    localparam JALR =   7'b1100111;
    wire [6:0] opcode ;
    assign opcode=inst[6:0];
    always @(*)
    case(opcode)
        IMM:    imm_o   =   {{20{inst[31]}},inst[31:20]};
        JALR:   imm_o   =   {{20{inst[31]}},inst[31:20]};
        STORE:  imm_o   =   {{20{inst[31]}} ,inst[31:25],inst[11:7]};
        LOAD:   imm_o   =   {{20{inst[31]}}, inst[31:20]};
        BEQ:    imm_o   =   {{20{inst[31]}},inst[31],inst[7],inst[30:25],inst[11:8]};
        AUIPC:  imm_o   =   {inst[31:12],12'b0};
        JAL:    imm_o   =   {{12{inst[31]}},inst[19:12],inst[20],inst[30:21],1'b0};
    endcase
endmodule

module Control(opcode, branch, mem_write, mem_to_reg, alu_op, alu_src, auipc, reg_write, jal,jalr);
    input [6:0] opcode;
    output reg branch, mem_write, mem_to_reg, alu_src, reg_write, auipc,jal,jalr;
    output reg [2:0] alu_op;
    localparam IMM  =   7'b0010011;
    localparam R    =   7'b0110011;
    localparam BEQ  =   7'b1100011;
    localparam LOAD =   7'b0000011;
    localparam STORE=   7'b0100011;
    localparam AUIPC=   7'b0010111;
    localparam JAL  =   7'b1101111;
    localparam JALR =   7'b1100111;

    always @(*) begin
    case(opcode)
    IMM:    begin
        branch = 1'b0;
        auipc = 1'b0;
        alu_src = 1'b1;
        reg_write = 1'b1;
        alu_op = 3'b011;
        jal = 1'b0;
        jalr = 1'b0;
        mem_write = 1'b0;
        mem_to_reg = 1'b0;
    end
    R:      begin
        branch = 1'b0;
        auipc = 1'b0;
        alu_src = 1'b0;
        reg_write = 1'b1;
        alu_op = 3'b010;
        jal = 1'b0;
        jalr = 1'b0;
        mem_write = 1'b0;
        mem_to_reg = 1'b0;
    end
    BEQ:    begin 
        branch = 1'b1;
        auipc = 1'b0;   
        alu_src = 1'b0;
        reg_write = 1'b0;
        alu_op = 3'b001;
        jal = 1'b0;
        jalr = 1'b0;
        mem_write = 1'b0;
        mem_to_reg = 1'b0;
    end
    LOAD:   begin
        branch = 1'b0;
        auipc = 1'b0;
        alu_src = 1'b1; 
        reg_write = 1'b1;
        alu_op = 3'b000;
        jal = 1'b0;
        jalr = 1'b0;        
        mem_to_reg = 1'b1;
        mem_write = 1'b0;
    end
    STORE:  begin 
        branch = 1'b0;
        auipc = 1'b0;     
        alu_src = 1'b1;
        reg_write = 1'b0;
        alu_op = 3'b000;
        jal = 1'b0;
        jalr = 1'b0;  
        mem_to_reg = 1'b0;
        mem_write = 1'b1;
    end
    AUIPC:  begin 
        branch = 1'b0;
        auipc = 1'b1;
        alu_src = 1'b1;
        reg_write = 1'b1;
        alu_op = 3'b011;
        jal = 1'b0;
        jalr = 1'b0;
        mem_write = 1'b0; 
        mem_to_reg = 1'b0;
    end
    JALR:   begin
        branch = 1'b0;
        auipc = 1'b0;
        alu_src = 1'b1;    
        reg_write = 1'b1;
        alu_op = 3'b000;
        jal = 1'b1; // jump
        jalr = 1'b1; // use rs
        mem_write = 1'b0;
        mem_to_reg = 1'b0;
    end
    JAL:    begin 
        branch = 1'b0;
        auipc = 1'b0;
        alu_src = 1'b1;
        reg_write = 1'b1;
        alu_op = 3'b000;
        jal = 1'b1; // jump
        jalr = 1'b0; // not use rs     
        mem_write = 1'b0;
        mem_to_reg = 1'b0;
    end
    default:begin
        branch = 1'b0;
        auipc = 1'b0;
        alu_src = 1'b0;
        reg_write = 1'b0;
        alu_op = 3'b0;
        jal = 1'b0; // jump
        jalr = 1'b0; // not use rs
        mem_write = 1'b0;
        mem_to_reg = 1'b0;
    end
    endcase 
    end

endmodule


module ALU_Control(func3,func7, alu_op, alu_inst, mul_op);
    input [2:0] func3;
    input [6:0] func7;
    input [2:0] alu_op;
    output [3:0] alu_inst;
    output mul_op;
    reg [3:0] alu_inst;
    reg mul_op;
    localparam  BEQ =   3'b001;
    localparam  LS  =   3'b000;
    localparam  IMM =   3'b011;
    localparam  R   =   3'b010;
    always@(*) begin
    case(alu_op)
    BEQ :    case(func3)
    3'b000: alu_inst = 4'b0110; //beq
    3'b101: alu_inst = 4'b1010; //bge
    endcase
    LS  : alu_inst = 4'b0010; //load,store
    IMM : case(func3)
        3'b000: alu_inst = 4'b0010; //addi
        3'b010: alu_inst = 4'b0111; //slti
        3'b001: alu_inst = 4'b1001; //slli                
        3'b101: alu_inst = 4'b1000; //srli
        default: alu_inst = 4'b0000;
        endcase
    R   : case({func7,func3})
        10'b0000000000: alu_inst = 4'b0010; //add
        10'b0100000000: alu_inst = 4'b0110; //sub
        10'b0000001000: alu_inst = 4'b0000; //mul
        10'b0000000100: alu_inst = 4'b0100; //xor
        default: alu_inst = 4'b0000;
        endcase
    default: alu_inst = 4'b0000;

    endcase

    if (alu_op == R && func7[0] == 1'b1) mul_op = 1'b1;
    else mul_op = 1'b0;
    
    end
endmodule


module ALU(data_1, data_2, alu_inst, data_out, zero);
    input [31:0] data_1, data_2;
    input [3:0] alu_inst;
    output [31:0] data_out;
    output zero;
    
    reg [31:0] data_out_r;
    assign data_out = data_out_r;

    assign zero = (data_out_r== 32'b0)? 1'b1:1'b0;
    always @(*) begin
        case(alu_inst)
            4'b0010: data_out_r = data_1 + data_2;
            4'b0100: data_out_r = data_1 ^ data_2;
            4'b0110: data_out_r = data_1 - data_2;
            4'b1010: data_out_r = (data_1 < data_2)? 32'b0:32'b1;
            4'b0111: data_out_r = (data_1 < data_2)? 32'b1:32'b0;
            4'b1000: data_out_r = data_1 >> data_2;
            4'b1001: data_out_r = data_1 << data_2;
            default: data_out_r = 32'b0;
        endcase
    end
endmodule


module mul(clk, rst_n, valid,in_A, in_B, done, mul_out);

    input         clk, rst_n;
    input         valid;
    input  [31:0] in_A, in_B;
    output  reg      done;
    output [31:0] mul_out;

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

    assign mul_out=shreg[31:0];
//FSM
//-------------------------------------------------------
    always @(*) begin
        case(state)
            IDLE: begin
                if (valid) begin
                    state_nxt = MUL;
                    done = 0;
                end
                else begin
                    state_nxt = IDLE;
                    done = 1;
                end
            end
            MUL : begin 
                if (counter == 5'd31) begin
                    state_nxt = OUT;
                    done = 0;
                end
                else begin
                    state_nxt = MUL;
                    done = 0;
                end
            end
            OUT : begin
                state_nxt = IDLE;
                done = 1;
            end
            default : begin
                state_nxt = OUT;
                done = 1;
        end
        endcase
        if(state == MUL) counter_nxt = counter + 1;
        else counter_nxt = 0;
    end
// load ALU input-->control:B
//-----------------------------------------------------
    always @(*) begin
    case(state)
    IDLE: begin           
        if (valid)  alu_in_nxt = in_B;
        else alu_in_nxt = 0;
    end
    OUT : alu_in_nxt = 0;
    default: alu_in_nxt = alu_in;
    endcase
    end
// ALU output
//------------------------------------------------------
    always @(*) begin
    case(state)
    MUL: begin
        if(shreg[0]==1) alu_out=shreg[63:32]+alu_in;
        else alu_out=shreg[63:32];
    end
    default: alu_out = 0;
    endcase
    end
//shift register
//-----------------------------------------------------------
    always @(*) begin
    case(state)
    IDLE: begin
            if (valid)  shreg_nxt = {32'b0,in_A};
            else shreg_nxt = 0;
    end
    MUL:    shreg_nxt={alu_out,shreg[31:1]};

    OUT:    shreg_nxt = shreg;
    default:shreg_nxt = 0;

    endcase
    end
//--------------------------------------------------------------------
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
//======================================================
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
