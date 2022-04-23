module ALU(
    clk,
    rst_n,
    valid,
    ready,
    mode,
    in_A,
    in_B,
    out
);

    // Definition of ports
    input         clk, rst_n;
    input         valid;
    input  [1:0]  mode; // mode: 0: mulu, 1: divu, 2: and, 3: avg
    output        ready;
    input  [31:0] in_A, in_B;
    output [63:0] out;

    // Definition of states
    parameter IDLE = 3'd0;
    parameter MUL  = 3'd1;
    parameter DIV  = 3'd2;
    parameter AND = 3'd3;
    parameter AVG = 3'd4;
    parameter OUT  = 3'd5;

    // Todo: Wire and reg if needed
    reg  [ 2:0] state, state_nxt;
    reg  [ 4:0] counter, counter_nxt;
    reg  [63:0] shreg, shreg_nxt;
    reg  [31:0] alu_in, alu_in_nxt;
    reg  [32:0] alu_out;
    reg  [63:0] out;   // reg for output "out"
    reg  [ 0:0] ready; // reg for output "ready"
    // Todo: Instatiate any primitives if needed
    reg  [32:0] temp;  // for AVG to check if in_A + in_B is positive or not
    // Todo 5: Wire assignments
    always @(*) begin
        if (state == 3'd5) begin
            case(mode)
                0: out = shreg[63:0]; // MUL(64 bits)
                1: out = shreg[63:0]; // DIV(64 bits)
                2: out = shreg[31:0]; // AND(32 bits)
                3: out = shreg[31:0]; // AVG(32 bits)
            endcase
            ready = 1;
        end else begin
            out = 0;
            ready = 0;
        end
    end
    // Combinational always block
    // Todo 1: Next-state logic of state machine
    always @(*) begin
        case(state)
            IDLE: begin
                if (valid) begin
                    case(mode)
                        0: state_nxt = MUL;
                        1: state_nxt = DIV;
                        2: state_nxt = AND;
                        3: state_nxt = AVG;
                    endcase
                end 
                else state_nxt = IDLE;
            end
            MUL: begin
                if(counter != 5'd31) state_nxt = MUL;
                else state_nxt = OUT;
            end
            DIV: begin
                if(counter != 5'd31) state_nxt = DIV;
                else state_nxt = OUT;
            end
            AND: state_nxt = OUT;
            AVG: state_nxt = OUT;
            OUT: state_nxt = IDLE;
            default : state_nxt = IDLE;
        endcase
    end
    // Todo 2: Counter
    always @(*) begin
        case(state)
            MUL: counter_nxt = counter + 1;
            DIV: counter_nxt = counter + 1;
            default: counter_nxt = 0;
        endcase
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
        case (state)
            AND: alu_out = shreg[31:0] & alu_in;
            AVG: begin
                temp = shreg[31:0] + alu_in;
                if (temp >= 0) alu_out = temp >> 1;
                else alu_out = {1'b1, temp[31:1]};
            end
            MUL: begin
                if (shreg[0] == 1'b1) alu_out = alu_in;
                else alu_out = 0;
            end
            DIV: alu_out = shreg[62:31] - alu_in;
            default: alu_out = 0;
        endcase
    end
    // Todo 4: Shift register
    always @(*) begin
        case(state)
        IDLE: begin
            if (valid) shreg_nxt = {32'b0, in_A};
            else shreg_nxt = 0;
        end
        AND: shreg_nxt = alu_out[31:0];
        AVG: shreg_nxt = alu_out[31:0];
        MUL: begin
            shreg_nxt = {shreg[63:32] + alu_out[31:0], shreg[31:0]} >> 1;
            if (shreg_nxt[62:31] < shreg[63:32]) shreg_nxt[63] = 1;
            else shreg_nxt[63] = 0;
        end
        DIV: begin
            if (alu_out[32] == 1) shreg_nxt = shreg << 1;
            else begin
                shreg_nxt = {1'b0, alu_out[31:0], shreg[30:0]} << 1;                                      
                shreg_nxt[0] = 1;
            end
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