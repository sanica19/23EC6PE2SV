//------------------------------------------------------------------------------
//File       : atm_controller.sv
//Author     : Sanica M S/1BM23EC229
//Created    : 04-02-2026
//Module     : atm_controller
//Project    : SystemVerilog and Verification (23EC6PE2SV),
//Faculty    : Prof. Ajaykumar Devarapalli
//Description: ATM Controller used for basic functional coverage example.
//------------------------------------------------------------------------------
`timescale 1ns/1ps

module atm_fsm (
  input  logic clk,
  input  logic rst,
  input  logic card_inserted,
  input  logic pin_correct,
  input  logic balance_ok,
  output logic dispense_cash
);

  // ---------------- STATE DEFINITION ----------------
  typedef enum logic [1:0] {
    IDLE       = 2'b00,
    CHECK_PIN  = 2'b01,
    CHECK_BAL  = 2'b10,
    DISPENSE  = 2'b11
  } state_t;

  state_t state, next_state;

  // ---------------- STATE REGISTER ----------------
  always_ff @(posedge clk or posedge rst) begin
    if (rst)
      state <= IDLE;
    else
      state <= next_state;
  end

  // ---------------- NEXT STATE LOGIC ----------------
  always_comb begin
    next_state = state;
    dispense_cash = 0;

    case (state)
      IDLE: begin
        if (card_inserted)
          next_state = CHECK_PIN;
      end

      CHECK_PIN: begin
        if (pin_correct)
          next_state = CHECK_BAL;
        else
          next_state = IDLE;
      end

      CHECK_BAL: begin
        if (balance_ok)
          next_state = DISPENSE;
        else
          next_state = IDLE;
      end

      DISPENSE: begin
        dispense_cash = 1;
        next_state = IDLE;
      end
    endcase
  end

  // ---------------- ASSERTIONS ----------------

  // Cash dispensed ONLY if pin correct AND balance ok
  property dispense_only_if_valid;
    @(posedge clk)
    dispense_cash |-> (pin_correct && balance_ok);
  endproperty

  assert property (dispense_only_if_valid)
    else $error("ERROR: Cash dispensed without valid PIN or balance");

  // Must return to IDLE after dispensing
  property return_to_idle;
    @(posedge clk)
    (state == DISPENSE) |=> (state == IDLE);
  endproperty

  assert property (return_to_idle)
    else $error("ERROR: FSM did not return to IDLE after DISPENSE");

endmodule
