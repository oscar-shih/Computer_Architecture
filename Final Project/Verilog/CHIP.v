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
assign mem_addr_I = PC;

// Todo: other wire/reg
reg [31:0] read_data;
assign rd_data = mem_rdata_D;
wire [31:0] imm,imm_shift;
wire [31:0] addr_D;
wire branch;
wire mem_to_reg;
wire [2:0] alu_op;
wire alu_src;
wire usepc_src;
wire jump_1;
wire jump_2;
wire [3:0] alu_inst;
wire [31:0] rs1_data_mux,rs2_data_mux;
wire [31:0] pc_next_0, pc_next_1,PC_normal,jump_data,jump_src,rd_temp;
wire [31:0] alu_out;
wire alu_zero;
wire pc_branch;
wire mem_d_use;
assign mem_addr_D = addr_D;
assign mem_wdata_D = rs2_data;
wire mul_ready;
wire [31:0] mul_output;
wire [31:0] rd_data_1;
wire doing_mul;
wire mul_op;


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
.wen(mem_wen_D),
.mem_to_reg(mem_to_reg), 
.alu_op(alu_op), 
.alu_src(alu_src),
.usepc_src(usepc_src), 
.reg_write(regWrite),
.jump_1(jump_1),
.jump_2(jump_2),
.mem_d_use(mem_d_use)
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


assign rs2_data_mux=alu_src? imm:rs2_data;
assign rs1_data_mux=usepc_src? PC :rs1_data;


ALU ALU(
.data_1(rs1_data_mux), 
.data_2(rs2_data_mux), 
.alu_inst(alu_inst), 
.data_out(alu_out), 
.zero(alu_zero)
);

assign imm_shift=imm<<1;

assign pc_next_0=PC+32'd4;
assign pc_next_1=PC+imm_shift;

assign pc_branch=branch &alu_zero;
assign PC_normal= pc_branch?  pc_next_1: pc_next_0;

assign jump_data=jump_2? rs1_data:PC;

assign jump_src=jump_data+imm;

assign PC_nxt= jump_1?jump_src:PC_normal;

assign rd_temp=mem_to_reg?mem_rdata_D:alu_out;

assign rd_data_1=jump_1?pc_next_0:rd_temp;

assign addr_D=mem_d_use?alu_out:{32{1'b0}};



mul mul(
.clk(clk),
.rst_n(rst_n),
.valid(mul_op),
.ready(mul_ready),
.in_A(rs1_data_mux),
.in_B(rs2_data_mux),
.doing_mul(doing_mul),
.out(mul_output)
);

assign rd_data=mul_op?mul_output:rd_data_1;


always @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
    PC <= 32'h00010000; // Do not modify this value!!!

    end
    else begin
    if (!doing_mul) begin
        PC <= PC_nxt;
    end
    else begin
        PC <= PC;
    end

    end
    end
endmodule

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

module Control(opcode, branch, wen, mem_to_reg, alu_op, alu_src, usepc_src, reg_write, jump_1,jump_2, mem_d_use);
    input [6:0] opcode;
    output reg branch, wen, mem_to_reg, alu_src, reg_write, usepc_src,jump_1,jump_2,mem_d_use;
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
        wen = 1'b1;
        mem_to_reg = 1'b0;
        alu_src = 1'b1;
        usepc_src = 1'b0;
        reg_write = 1'b1;
        alu_op = 3'b011;
        jump_1 = 1'b0;
        jump_2 = 1'b0;
        mem_d_use = 1'b0;
    end
    R:      begin
        branch = 1'b0;
        wen = 1'b1;
        mem_to_reg = 1'b0;
        alu_src = 1'b0;
        usepc_src = 1'b0;
        reg_write = 1'b1;
        alu_op = 3'b010;
        jump_1 = 1'b0;
        jump_2 = 1'b0;
        mem_d_use = 1'b0;
    end
    BEQ:    begin 
        branch = 1'b1;
        wen = 1'b1;
        mem_to_reg = 1'b0;
        alu_src = 1'b0;
        usepc_src = 1'b0;
        reg_write = 1'b0;
        alu_op = 3'b001;
        jump_1 = 1'b0;
        jump_2 = 1'b0;
        mem_d_use = 1'b0;
    end
    LOAD:   begin
        branch = 1'b0;
        wen = 1'b0;
        mem_to_reg = 1'b1;
        alu_src = 1'b1;
        usepc_src = 1'b0;
        reg_write = 1'b1;
        alu_op = 3'b000;
        jump_1 = 1'b0;
        jump_2 = 1'b0;
        mem_d_use = 1'b1;
    end
    STORE:  begin 
        branch = 1'b0;
        wen = 1'b1;
        mem_to_reg = 1'bx;
        alu_src = 1'b1;
        usepc_src = 1'b0;
        reg_write = 1'b0;
        alu_op = 3'b000;
        jump_1 = 1'b0;
        jump_2 = 1'b0;
        mem_d_use = 1'b1;
    end
    AUIPC:  begin 
        branch = 1'b0;
        wen = 1'b1;
        mem_to_reg = 1'b0;
        alu_src = 1'b1;
        usepc_src = 1'b1;
        reg_write = 1'b1;
        alu_op = 3'b011;
        jump_1 = 1'b0;
        jump_2 = 1'b0;
        mem_d_use = 1'b0;
    end
    JALR:   begin
        branch = 1'b0;
        wen = 1'b1;
        mem_to_reg = 1'b0;
        alu_src = 1'b1;
        usepc_src = 1'b0;
        reg_write = 1'b1;
        alu_op = 3'b000;
        jump_1 = 1'b1; // jump
        jump_2 = 1'b1; // use rs
        mem_d_use = 1'b0;
    end
    JAL:    begin // jal
        branch = 1'b0;
        wen = 1'b1;
        mem_to_reg = 1'b0;
        alu_src = 1'b1;
        usepc_src = 1'b0;
        reg_write = 1'b1;
        alu_op = 3'b000;
        jump_1 = 1'b1; // jump
        jump_2 = 1'b0; // not use rs
        mem_d_use = 1'b0;
    end
    default:begin
        branch = 1'b0;
        wen = 1'b0;
        mem_to_reg = 1'b0;
        alu_src = 1'b0;
        usepc_src = 1'b0;
        reg_write = 1'b0;
        alu_op = 3'b0;
        jump_1 = 1'b0; // jump
        jump_2 = 1'b0; // not use rs
        mem_d_use = 1'b0;
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
    case(alu_op)// beq ld imm r 
    BEQ : case(func3)
        3'b000: alu_inst = 4'b0110; //beq
        3'b101: alu_inst = 4'b1010; //bge
        endcase
    LS  : alu_inst = 4'b0010; //ld,sd
    IMM : case(func3)//imm //func3
        3'b000: alu_inst = 4'b0010; //addi
        3'b010: alu_inst = 4'b0111; //slti
        3'b001: alu_inst = 4'b1001; //slli                
        3'b101: alu_inst = 4'b1000; //srli
        
        default: alu_inst = 4'b0000;
        endcase
    R   : case({func7,func3})//r 
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
            4'b1010: data_out_r = (data_1 >= data_2)? 32'b0:32'b1;
            4'b0111: data_out_r = (data_1 < data_2)? 32'b1:32'b0;
            4'b1000: data_out_r = data_1 >> data_2;
            4'b1001: data_out_r = data_1 << data_2;
            default: data_out_r = {32{1'b0}};
        endcase
    end
endmodule



module mul(clk, rst_n, valid, ready, doing_mul, in_A, in_B, out);

    input         clk, rst_n;
    input         valid;
    output        ready,doing_mul;
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
    reg  [32:0] B, B_nxt;
    reg  [31:0] out;
    reg         ready;
    reg         doing_mul;
    always @(*) begin
    if (state == 3'd2) begin
    out = shreg[31:0];
    ready = 1;
    end
    else begin
    out = 0;
    ready = 0;
    end
    end

    always @(*) begin
    case(state)
    IDLE: begin
        B_nxt = in_B;
        if (valid) begin
            state_nxt = MUL;
            doing_mul = 1;
        end
        else begin
            state_nxt = IDLE;
            doing_mul = 0;
        end
    end
    MUL : begin 
        B_nxt = B;
        if (counter != 5'd31) begin
            state_nxt = MUL;
            doing_mul = 1;
        end
        else begin
            state_nxt = OUT;
            doing_mul = 1;
        end
    end
    OUT : begin
        B_nxt = B;
        state_nxt = IDLE;
        doing_mul = 0;
    end
    default : begin
        B_nxt = B;
        state_nxt = IDLE;
        doing_mul = 0;
    end
    endcase
    end

    always @(*) begin
    case(state)
    MUL : begin
        counter_nxt = counter + 1;
    end
    default: begin
        counter_nxt = 0;
    end            
    endcase
    end

    always @(*) begin
    case(state)
    OUT : begin
        alu_in_nxt = 0;
    end
    default: begin           
        if (valid) begin
            alu_in_nxt = B_nxt;
        end
        else begin
            alu_in_nxt = alu_in;
        end
    end
    endcase
    end

    always @(*) begin
    case(state)
    MUL: begin
        if (shreg[0] == 1'b1) alu_out = alu_in;
        else alu_out = 0;
    end
    default: alu_out = 0;
    endcase
    end

    always @(*) begin
    case(state)
    IDLE: begin
        if (valid) begin
            shreg_nxt = {32'b0,in_A};
        end
        else begin
            shreg_nxt = 0;
        end
    end
    MUL: begin
        shreg_nxt = {shreg[63:32]+alu_out[31:0],shreg[31:0]} >> 1;
        if (shreg_nxt[62:31] < shreg[63:32]) shreg_nxt[63] = 1;
        else shreg_nxt[63] = 0;
    end
    default: begin
        shreg_nxt = 0;
    end
    endcase
    end

    always @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
    state <= IDLE;
    B     <= 32'b0;
    end
    else begin
    state <= state_nxt;
    counter <= counter_nxt;
    shreg <= shreg_nxt;
    alu_in <= alu_in_nxt;
    B      <= B_nxt;
    end
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
// // Your code
// module CHIP(clk,
//             rst_n,
//             // For mem_D
//             mem_wen_D,
//             mem_addr_D,
//             mem_wdata_D,
//             mem_rdata_D,
//             // For mem_I
//             mem_addr_I,
//             mem_rdata_I);

//     input         clk, rst_n ;
//     // For mem_D
//     output        mem_wen_D  ;
//     output [31:0] mem_addr_D ;
//     output [31:0] mem_wdata_D;

//     input  [31:0] mem_rdata_D;
//     // For mem_I
//     output [31:0] mem_addr_I ;
//     input  [31:0] mem_rdata_I;
    
//     //---------------------------------------//
//     // Do not modify this part!!!            //
//     // Exception: You may change wire to reg //
//     reg    [31:0] PC          ;              //
//     wire   [31:0] PC_nxt      ;              //
//     wire          regWrite    ;              //
//     wire   [ 4:0] rs1, rs2, rd;              //
//     wire   [31:0] rs1_data    ;              //
//     wire   [31:0] rs2_data    ;              //
//     wire   [31:0] rd_data     ;              //
//     //---------------------------------------//

//     // Todo: other wire/reg
//     //contol
//     wire branch, mem_read, mem_to_reg, alu_src;//control
//     wire [1:0] alu_op;//alu_op 2 bits
    
//     // alu input
//     wire [11:0] alu_inst;
//     wire [31:0] in1,in2;
//     wire [31:0] alu_result;
//     wire zero;
    
//     //  mul
//     wire mul_valid,ready;
//     wire [31:0] mul_out;

//     //  imm
//     wire    [31:0] imm_o;

//     //  ref_file
//     assign rs1  = mem_rdata_I[19:15];//rs1
//     assign rs2  = mem_rdata_I[24:20];//rs2
//     assign rd   = mem_rdata_I[11: 7];//rd

//     //write back
//     assign rd_data = mem_to_reg ? alu_result:mem_rdata_D;

//     reg        mem_wen_D_r ;
//     reg [31:0] mem_addr_D_r;
//     reg [31:0] mem_wdata_D_r;
//     reg [31:0] mem_addr_I_r;

//     //---------------------------------------//
//     // Do not modify this part!!!            //
//     reg_file reg0(                           //
//         .clk(clk),                           //
//         .rst_n(rst_n),                       //
//         .wen(regWrite),                      //
//         .a1(rs1),                            //
//         .a2(rs2),                            //
//         .aw(rd),                             //
//         .d(rd_data),                         //
//         .q1(rs1_data),                       //
//         .q2(rs2_data));                      //
//     //---------------------------------------//

//     // Todo: any combinational/sequential circuit
//     //  imm
//     imm_generator u_imm_generator(.inst(mem_rdata_I), .imm_o(imm_o));
//     //  control
//     Control u_Control(.inst(mem_rdata_I[6:0]), .branch(branch), .mem_read(mem_read), 
//     .mem_to_reg(mem_to_reg), .alu_op(alu_op), .mem_write(mem_wen_D), .alu_src(alu_src), .reg_writerite(regWrite));
//     ALU_control u_ALUcontrol( .inst(mem_rdata_I), .alu_op(alu_op), .alu_inst(alu_inst), .mul_valid(mul_valid));

//     //alu_src
//     assign in1 = rs1_data;
//     assign in2 = alu_src ? imm_o :  rs2_data;

//     //  ALU
//     ALU u_ALU(.in1(in1), .in2(in2), .alu_inst(alu_inst), .alu_result(alu_result),.zero( zero));
    
//     mulDiv u_mulDiv(.clk(clk), .rst_n(rst_n), .valid(mul_valid), .ready(ready), .in_A(in1), .in_B(in2), .out(mul_out));




//     //-----------------------------------------------------------------------//
//     //-----------------PC---------------//
//     reg [31:0] pc_4,pc_branch;
//     always @(*) begin
//        if(ready) begin 
//             pc_4=PC+4;
//             pc_branch=PC+(imm_o<<1);
//         end
//         else begin 
//             pc_4=PC;
//             pc_branch=PC;
//        end
//     end
//     assign PC_nxt=branch ? pc_4:pc_branch;

//     assign  mem_addr_I  =   mem_addr_I_r;
//     assign  mem_addr_D  =   mem_addr_D_r;
//     assign  mem_wdata_D =   mem_wdata_D_r   ;   

//     always @(posedge clk or negedge rst_n) begin
//         if (!rst_n) begin
//             PC <= 32'h00010000; // Do not modify this value!!!
            
//         end
//         else begin
//             PC <= PC_nxt;
            
//         end
//         mem_addr_I_r=PC;
//         if(mul_valid) begin
//             mem_addr_D_r=mul_out;
//         end
//         else begin
//             mem_addr_D_r=alu_result;
//         end
//         mem_wdata_D_r=rs2_data;


//     end


// endmodule

// //-------------------------------------------------------//

// // module input_generator(
// //     input  [31:0] q1,
// //     input  [31:0] q2,
// //     input  [31:0] inst,
// //     input         alu_src,
// //     input  [31:0] now_pc,

// //     output [31:0] in1,
// //     output [31:0] in2
// // );
// //     wire    [31:0] imm_o;
// //     reg     [31:0] alu_data1,  alu_data2;
// //     imm_generator u_imm_generator(inst, imm_o);
// //     // parameters for alu_op from Control Unit
// //     parameter LUI   = 7'b0110111;
// //     parameter AUIPC = 7'b0010111;
// //     parameter JAL   = 7'b1101111;
// //     parameter JALR  = 7'b1100111;
// //     always @(*) begin
// //         case({inst[6:0]}):
// //             LUI:        alu_data1 = {imm_o[19:0],12'b0};
// //             AUIPC:      alu_data1 = {imm_o[19:0],12'b0};
// //             JAL:        alu_data1 = now_pc;
// //             JALR:       alu_data1 = now_pc;
// //             default:    alu_data1 = q1;
// //         endcase
// //         case({inst[6:0]}):
// //             LUI:        alu_data2 = 32'b0;
// //             AUIPC:      alu_data2 = now_pc;
// //             JAL:        alu_data2 = 32'd4;
// //             JALR:       alu_data2 = 32'd4;
// //             default:    alu_data2 = q2;
// //         endcase
// //     end
// //     assign in1 =  alu_data1;
// //     assign in2 = alu_src ? imm_o :  alu_data2;
// // endmodule



// //---------------------------------------------------------------------------//
// module imm_generator(inst, imm_o);
//     input [31:0] inst;
//     output reg[31:0] imm_o;
//     always @(*) begin//inst) begin
//         case(inst[6:0])
//             // lui, auipc
//             7'b0110111: imm_o = {inst[31:12], {12{1'b0}}};
//             // jal
//             7'b1101111: imm_o = {{11{inst[31]}}, inst[31], inst[19:12], inst[20], inst[30:21], 1'b0};
//             // jalr
//             7'b1100111: imm_o = {{20{inst[31]}}, inst[31:20]};
//             // branch instruction: beq, bne, blt, bge, bltu, bgeu
//             7'b1100011: imm_o = {{19{inst[31]}}, inst[31], inst[7], inst[30:25], inst[11:8], 1'b0};
//             // Load instruction: lb, lh, lw, lbu, lhu 
//             7'b0000011: imm_o = {{20{inst[31]}}, inst[31:20]};
//             // Store instruction: sb sh, sw
//             7'b0100011: imm_o = {{20{inst[31]}}, inst[31:25], inst[11:7]}; 
//             // Logical gates: addi, slti, sltiu, xori, ori, andi
//             7'b0010011: imm_o = {{20{inst[31]}}, inst[31:20]};
//             // slli, srli, srai (shampt, 0~31)
//             7'b0010011: imm_o = {27'b0, inst[24:20]};
//             default: imm_o = {32{1'b0}};
//         endcase
//     end
// endmodule

// //------------------------------------------------------------------//
// module ALU(in1, in2, alu_inst, alu_result, zero);
//     input signed [31:0] in1, in2;
//     input   [11:0] alu_inst;

//     output  [31:0] alu_result;
//     output zero;

//     reg [31:0] result;
//     reg zero_r;
//     assign alu_result = result;
//     assign zero = zero_r;
//     // parameters for alu_inst from ALU_Control Unit (f7[5] + f3 + opc)
//     parameter LS    = 12'b0; // jalr jal auipc lui ld sd

//     parameter BEQ   = 12'b00_000_1100011; // sub
//     parameter BNE   = 12'b00_001_1100011; // sub
//     parameter BLT   = 12'b00_100_1100011; // sub
//     parameter BGE   = 12'b00_101_1100011; // sub

//     parameter ADDI  = 12'bxx_000_0010011; // func
    
//     parameter ADD   = 12'b00_000_0110011; // func
//     parameter SUB   = 12'b10_000_0110011; // func

//     parameter SLTI  = 12'bxx_010_0010011; // func
//     parameter SRLI  = 12'bxx_101_0010011; // func
//     parameter SLLI  = 12'bxx_001_0010011; // func


//     always @(*) begin//in1 or in2 or alu_inst) begin
//         //result
//         case(alu_inst)
//             LS:   result = in1 + in2;
//             // addi
//             ADDI: result = in1 + in2;
//             // beq
//             BEQ:  result = in1 - in2;
//             // bne
//             BNE:  result = in1 - in2;
//             //blt
//             BLT:  result = in1 - in2;
//             //bge
//             BGE:  result = in1 - in2;
//             // 
//             ADD:  result = in1 + in2;
//             SUB:  result = in1 - in2;
//             //
//             SLTI: result = (in1 < in2) ? 1'b1 : 1'b0;
//             SRLI: result = in1 >> in2;
//             SLLI: result = in1 << in2;
//             default: result = in1 + in2;
//         endcase
//         //zero
//         case(alu_inst)
//             // beq
//             BEQ: zero_r = (result == 32'b0)     ? 1'b1 : 1'b0;
//             // bne
//             BNE: zero_r = (result != 32'b0)     ? 1'b1 : 1'b0;
//             //blt
//             BLT: zero_r = (result[31] != 1'b0)  ? 1'b1 : 1'b0;
//             //bge
//             BGE: zero_r = (result[31] == 1'b0)  ? 1'b1 : 1'b0;
//             default: zero_r = (result == 32'b0) ? 1'b1 : 1'b0;
//         endcase
//     end
// endmodule


// //---------------------------------------------------------------------//
// module ALU_control(inst, alu_op, alu_inst, mul_valid);
//     input   [31:0]  inst;
//     input   [ 1:0]  alu_op;
//     output  [11:0]  alu_inst;
//     output          mul_valid; // for the valid in mulDiv

//     reg [11:0] alu;
//     reg mul_valid_r;

//     assign alu_inst = alu;
//     assign mul_valid = mul_valid_r;

//     // parameters for alu_op from Control Unit
//     parameter R  = 2'b10; 
//     parameter B  = 2'b01; 
//     parameter LS = 2'b00; 

//     always @(*) begin
//         case (alu_op)
//             R: alu = {inst[30],inst[25], inst[14:12], inst[6:0]};
//             B: alu = {2'b0, inst[14:12], inst[6:0]};
//             LS: alu = 12'b0;
//             default:alu=12'b0;
//         endcase
       
//         if (inst[6:0] == 7'b0110011 && inst[31:25] == 7'b0000001) mul_valid_r = 1'b1;
//         else mul_valid_r = 1'b0;
//     end
// endmodule

// //----------------------------------------------------------------------------------------//
// module Control(inst, branch, mem_read, mem_to_reg, alu_op, mem_write, alu_src, reg_write);
   
//     input [6:0] inst;
//     output reg branch, mem_read, mem_to_reg, mem_write, alu_src, reg_write;
//     output reg [1:0] alu_op;
//     // parameters for alu_op 
//     parameter RI = 2'b10;   // look at funct
//     parameter B  = 2'b01;   // Substract
//     parameter LS = 2'b00;   // ADD
//     // parameter for inst
//     parameter LUI =   7'b0110111;
//     parameter AUIPC = 7'b0010111;
//     parameter JAL   = 7'b1101111;
//     parameter JALR  = 7'b1100111;
//     parameter BBB   = 7'b1100011;
//     parameter LLL   = 7'b0000011;
//     parameter SSS   = 7'b0100011;
//     parameter IMM   = 7'b0010011;
//     parameter LOGIC = 7'b0110011;


//     always @(*) begin
//         case(inst)
//             // I
//             LUI: begin
//                 branch = 1'b0;
//                 mem_read = 1'b1;
//                 mem_to_reg = 1'b1; 
//                 mem_write = 1'b0; 
//                 alu_src = 1'b1;
//                 reg_write = 1'b1;
//                 alu_op = LS;
//             end
//             // I
//             AUIPC: begin
//                 branch = 1'b0;
//                 mem_read = 1'b1;
//                 mem_to_reg = 1'b1; 
//                 mem_write = 1'b0; 
//                 alu_src = 1'b1;
//                 reg_write = 1'b1;
//                 alu_op = LS;
//             end
//             // J
//             JAL: begin
//                 branch = 1'b1;
//                 mem_read = 1'b0;
//                 mem_to_reg = 1'b0; 
//                 mem_write = 1'b0; 
//                 alu_src = 1'b1;
//                 reg_write = 1'b1;
//                 alu_op = LS;
//             end
//             // I
//             JALR: begin
//                 branch = 1'b1;
//                 mem_read = 1'b0;
//                 mem_to_reg = 1'b0; 
//                 mem_write = 1'b0; 
//                 alu_src = 1'b0;
//                 reg_write = 1'b1;
//                 alu_op = LS;
//             end
//             // B
//             BBB: begin
//                 branch = 1'b1;
//                 mem_read = 1'b0;
//                 mem_to_reg = 1'b0; 
//                 mem_write = 1'b0; 
//                 alu_src = 1'b0;
//                 reg_write = 1'b0;
//                 alu_op = B;
//             end
//             // I
//             LLL: begin
//                 branch = 1'b0;
//                 mem_read = 1'b1;
//                 mem_to_reg = 1'b1; 
//                 mem_write = 1'b0; 
//                 alu_src = 1'b1;
//                 reg_write = 1'b1;
//                 alu_op = LS;
//             end
//             SSS: begin
//                 branch = 1'b0;
//                 mem_read = 1'b0;
//                 mem_to_reg = 1'b0; 
//                 mem_write = 1'b1; 
//                 alu_src = 1'b1;
//                 reg_write = 1'b0;
//                 alu_op = LS;
//             end
//             IMM: begin
//                 branch = 1'b0;
//                 mem_read = 1'b0;
//                 mem_to_reg = 1'b0; 
//                 mem_write = 1'b0; 
//                 alu_src = 1'b1;
//                 reg_write = 1'b1;
//                 alu_op = RI;
//             end
//             LOGIC: begin
//                 branch = 1'b0;
//                 mem_read = 1'b0;
//                 mem_to_reg = 1'b0; 
//                 mem_write = 1'b0; 
//                 alu_src = 1'b0;
//                 reg_write = 1'b1;
//                 alu_op = RI;
//             end
//             default: begin
//                 branch = 1'b0;
//                 mem_read = 1'b0;
//                 mem_to_reg = 1'b0; 
//                 mem_write = 1'b0; 
//                 alu_src = 1'b0;
//                 reg_write = 1'b0;
//                 alu_op = 2'b11;
//             end
//         endcase
//     end
// endmodule

// //-----------------------------------------------------------//
// module reg_file(clk, rst_n, wen, a1, a2, aw, d, q1, q2);

//     parameter BITS = 32;
//     parameter word_depth = 32;// 32 bits word
//     parameter addr_width = 5; // 2^addr_width >= word_depth

//     input clk, rst_n, wen; // wen=Regwrite:  0:read / 1:write
//     input [BITS-1:0] d;
//     input [addr_width-1:0] a1, a2, aw;//rs1,rs2,rd

//     output [BITS-1:0] q1, q2;//data in rsi,rs2

//     reg [BITS-1:0] mem [0:word_depth-1];
//     reg [BITS-1:0] mem_nxt [0:word_depth-1];

//     integer i;

//     assign q1 = mem[a1];
//     assign q2 = mem[a2];

//     always @(*) begin
//         for (i=0; i<word_depth; i=i+1)
//             mem_nxt[i] = (wen && (aw == i)) ? d : mem[i];
//     end

//     always @(posedge clk or negedge rst_n) begin
//         if (!rst_n) begin
//             mem[0] <= 0;
//             for (i=1; i<word_depth; i=i+1) begin
//                 case(i)
//                     32'd2: mem[i] <= 32'hbffffff0;
//                     32'd3: mem[i] <= 32'h10008000;
//                     default: mem[i] <= 32'h0;
//                 endcase
//             end
//         end
//         else begin
//             mem[0] <= 0;
//             for (i=1; i<word_depth; i=i+1)
//                 mem[i] <= mem_nxt[i];
//         end
//     end
// endmodule


// module mulDiv(clk, rst_n, valid, ready,in_A, in_B, out);
//     // Todo: your HW2
//     input         clk, rst_n;
//     input         valid;
//     input  [31:0] in_A, in_B;
//     output reg        ready;
//     output reg [31:0] out;

//     // Definition of states
//     parameter IDLE = 3'd0;
//     parameter MUL  = 3'd1;
//     parameter OUT  = 3'd2;

//     // Todo: Wire and reg if needed
//     reg  [ 2:0] state, state_nxt;
//     reg  [ 4:0] counter, counter_nxt;
//     reg  [63:0] shreg, shreg_nxt;
//     reg  [31:0] alu_in, alu_in_nxt;
//     reg  [32:0] alu_out;
//     //reg  [31:0] out;   // reg for output "out"

//     always @(*) begin
//         if (state == OUT) begin
//             out = shreg[31:0];
//             ready = 1;
//         end 
//         else begin
//             out = 0;
//             if(!valid) begin
//                 ready = 1;
//             end
//             else begin
//                 ready=0;
//             end
            
//         end

//     end

//     // Combinational always block
//     // Todo 1: Next-state logic of state machine
//     always @(*) begin
//         case(state)
//             IDLE: begin
//                 if (valid) state_nxt = MUL;
//                 else state_nxt = IDLE;
//             end
//             MUL: begin
//                 if(counter != 5'd31) state_nxt = MUL;
//                 else state_nxt = OUT;
//             end
//             default : state_nxt = IDLE;
//         endcase
//     end

//     // Todo 2: Counter
//     always @(*) begin
//         if(state == MUL) counter_nxt = counter + 1;
//         else counter_nxt = 0;
//     end

//     // ALU input
//     always @(*) begin
//         case(state)
//             IDLE: begin
//                 if (valid) alu_in_nxt = in_B;
//                 else       alu_in_nxt = 0;
//             end
//             OUT : alu_in_nxt = 0;
//             default: alu_in_nxt = alu_in;
//         endcase
//     end

//     // Todo 3: ALU output
//     always @(*) begin
//         if (state == MUL) begin
//             if (shreg[0] == 1'b1) alu_out = alu_in;
//             else alu_out = 0;
//         end
//         else alu_out = 0;
//     end

//     // Todo 4: Shift register
//     always @(*) begin
//         case(state)
//             IDLE: begin
//                 if (valid) shreg_nxt = {32'b0, in_A};
//                 else shreg_nxt = 0;
//             end
//             MUL: begin
//                 shreg_nxt = {shreg[63:32] + alu_out[31:0], shreg[31:0]} >> 1;
//                 if (shreg_nxt[62:31] < shreg[63:32]) shreg_nxt[63] = 1;
//                 else shreg_nxt[63] = 0;
//             end
//             default: shreg_nxt = 0;
//         endcase
//     end

//     // Todo: Sequential always block
//     always @(posedge clk or negedge rst_n) begin
//         if (!rst_n) begin
//             state <= IDLE;
//         end
//         else begin
//             state <= state_nxt;
//             counter <= counter_nxt;
//             shreg <= shreg_nxt;
//             alu_in <= alu_in_nxt;
//         end
//     end

// endmodule
