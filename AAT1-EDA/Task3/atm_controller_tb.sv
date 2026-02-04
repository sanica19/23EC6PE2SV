//------------------------------------------------------------------------------
//File       : atm_controller_tb.sv
//Author     : Sanica M S/1BM23EC229
//Created    : 04-02-2026
//Module     : atm_controller_tb
//Project    : SystemVerilog and Verification (23EC6PE2SV),
//Faculty    : Prof. Ajaykumar Devarapalli
//Description: ATM Controller used for basic functional coverage example.
//------------------------------------------------------------------------------
`timescale 1ns/1ps

module atm_fsm_tb;

  logic clk;
  logic rst;
  logic card_inserted;
  logic pin_correct;
  logic balance_ok;
  logic dispense_cash;

  // DUT
  atm_fsm dut (
    .clk(clk),
    .rst(rst),
    .card_inserted(card_inserted),
    .pin_correct(pin_correct),
    .balance_ok(balance_ok),
    .dispense_cash(dispense_cash)
  );

  // ---------------- CLOCK ----------------
  initial clk = 0;
  always #10 clk = ~clk;   // 20 ns clock (slow & readable)

  // ---------------- DUMP ----------------
  initial begin
    $dumpfile("atm_fsm.vcd");
    $dumpvars(0, atm_fsm_tb);
  end

  // ---------------- TEST SEQUENCE ----------------
  initial begin
    // Initialize
    rst = 1;
    card_inserted = 0;
    pin_correct = 0;
    balance_ok = 0;
    #25;

    rst = 0;

    // ---- VALID TRANSACTION ----
    card_inserted = 1;
    #20;
    card_inserted = 0;

    pin_correct = 1;
    #20;

    balance_ok = 1;
    #40;

    // ---- INVALID PIN ----
    pin_correct = 0;
    balance_ok = 0;
    card_inserted = 1;
    #20;
    card_inserted = 0;
    #40;

    // ---- INVALID BALANCE ----
    pin_correct = 1;
    balance_ok = 0;
    card_inserted = 1;
    #20;
    card_inserted = 0;
    #40;

    $finish;
  end

endmodule
