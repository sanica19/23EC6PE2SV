//------------------------------------------------------------------------------
// File       : atm.sv
// Author     : Sanica M S/ 1BM23EC229
// Project    : SystemVerilog and Verification (23EC6PE2SV)
// Description: atm
//------------------------------------------------------------------------------
//Top module
module Top;

alu_if vif();

ALU dut(
    .a(vif.a),
    .b(vif.b),
    .opcode(vif.opcode),
    .result(vif.result)
);

ALU_tb tb(vif);

endmodule
//TB
module ALU_tb(alu_if vif);

initial begin
    $shm_open("waves.shm");
    $shm_probe("AS", Top.dut);

    // ADD
    vif.a = 10; vif.b = 5; vif.opcode = 0; #10;

    // SUB
    vif.a = 10; vif.b = 3; vif.opcode = 1; #10;

    // MUL
    vif.a = 4; vif.b = 5; vif.opcode = 2; #10;

    // XOR
    vif.a = 8; vif.b = 3; vif.opcode = 3; #10;

    // repeat operations
    repeat(20) begin
        vif.a = $random;
        vif.b = $random;
        vif.opcode = $random % 4;
        #10;
    end

    $finish;
end

endmodule
//interface
interface alu_if;
    logic [31:0] a, b;
    logic [1:0] opcode;
    logic [31:0] result;
endinterface
module ALU(
    input logic [31:0] a,
    input logic [31:0] b,
    input logic [1:0] opcode,
    output logic [31:0] result
);

always_comb begin
    case(opcode)
        2'b00: result = a + b;
        2'b01: result = a - b;
        2'b10: result = a * b;
        2'b11: result = a ^ b;
        default: result = 0;
    endcase
end

endmodule

//design
module ATM(
    input logic clk,
    input logic reset,
    input logic card_inserted,
    input logic pin_correct,
    input logic balance_ok,
    output logic dispense_cash
);

typedef enum logic [1:0] {
    IDLE,
    CHECK_PIN,
    CHECK_BAL,
    DISPENSE
} state_t;

state_t state, next_state;

always_ff @(posedge clk or posedge reset) begin
    if(reset)
        state <= IDLE;
    else
        state <= next_state;
end

always_comb begin
    dispense_cash = 0;

    case(state)
        IDLE:
            next_state = card_inserted ? CHECK_PIN : IDLE;

        CHECK_PIN:
            next_state = pin_correct ? CHECK_BAL : IDLE;

        CHECK_BAL:
            next_state = balance_ok ? DISPENSE : IDLE;

        DISPENSE: begin
            dispense_cash = 1;
            next_state = IDLE;
        end
    endcase
end

endmodule
module ATM_tb(atm_if vif);

initial begin
    $shm_open("waves.shm");
    $shm_probe("AS", Top.dut);

    //---------------- RESET -------------//
    vif.reset = 1;
    vif.card_inserted = 0;
    vif.pin_correct = 0;
    vif.balance_ok = 0;
    #20;
    vif.reset = 0;

    //---------------- Case 1: correct flow --------//
    vif.card_inserted = 1;
    #20;

    vif.pin_correct = 1;
    #20;

    vif.balance_ok = 1;
    #20;

    vif.card_inserted = 0;
    vif.pin_correct = 0;
    vif.balance_ok = 0;
    #40;

    //---------------- Case 2: wrong PIN -----------//
    vif.card_inserted = 1;
    #20;

    vif.pin_correct = 0;
    #40;

    vif.card_inserted = 0;
    #20;

    //---------------- Case 3: insufficient balance //
    vif.card_inserted = 1;
    #20;

    vif.pin_correct = 1;
    #20;

    vif.balance_ok = 0;
    #40;

    vif.card_inserted = 0;
    #20;

    //---------------- Case 4: reset mid-transaction //
    vif.card_inserted = 1;
    #20;

    vif.reset = 1;
    #20;
    vif.reset = 0;

    //---------------- repeat transitions --------//
    repeat(5) begin
        vif.card_inserted = 1;
        #10;
        vif.pin_correct = $random;
        vif.balance_ok = $random;
        #20;

        vif.card_inserted = 0;
        vif.pin_correct = 0;
        vif.balance_ok = 0;
        #20;
    end

    $display("ATM TEST COMPLETED");
    #20 $finish;
end

endmodule
interface atm_if;
    logic clk;
    logic reset;
    logic card_inserted;
    logic pin_correct;
    logic balance_ok;
    logic dispense_cash;
endinterface
interface atm_if;
    logic clk;
    logic reset;
    logic card_inserted;
    logic pin_correct;
    logic balance_ok;
    logic dispense_cash;
endinterface
module Top;

atm_if vif();

initial begin
    vif.clk = 0;
    forever #5 vif.clk = ~vif.clk;
end

ATM dut(
    .clk(vif.clk),
    .reset(vif.reset),
    .card_inserted(vif.card_inserted),
    .pin_correct(vif.pin_correct),
    .balance_ok(vif.balance_ok),
    .dispense_cash(vif.dispense_cash)
);

ATM_tb tb(vif);

endmodule
