//------------------------------------------------------------------------------
//File       : alu.sv
//Author     : Sanica M S/1BM23EC229
//Created    : 04-02-2026
//Module     : alu
//Project    : SystemVerilog and Verification (23EC6PE2SV),
//Faculty    : Prof. Ajaykumar Devarapalli
//Description: 2-input 8-bit ALU used for basic functional coverage example.
//------------------------------------------------------------------------------
`timescale 1ns/1ps
import alu_pkg::*;

module alu_tb;

  logic [7:0]  a, b;
  opcode_e     op;
  logic [15:0] result;

  // DUT
  alu dut (
    .a(a),
    .b(b),
    .op(op),
    .result(result)
  );

  alu_transaction tr;

  // ---------------- COVERAGE ----------------
  covergroup alu_cg;
    coverpoint op {
      bins add_op = {ADD};
      bins sub_op = {SUB};
      bins mul_op = {MUL};
      bins xor_op = {XOR};
    }
  endgroup

  alu_cg cg;

  // ---------------- DUMP ----------------
  initial begin
    $dumpfile("alu.vcd");
    $dumpvars(0, alu_tb);
  end

  // ---------------- TEST ----------------
  initial begin
    tr = new();
    cg = new();

    // Initialize signals
    a  = 0;
    b  = 0;
    op = ADD;
    #10;

    repeat (50) begin
      // Randomize transaction
      assert(tr.randomize())
        else $fatal("Randomization failed");

      // Drive inputs
      a  = tr.a;
      b  = tr.b;
      op = tr.op;

      // Allow DUT to settled
      #5;

      // Sample coverage AFTER result is stable
      cg.sample();

      // Hold values so waveform is readable
      #5;
    end

    $display("Functional Coverage = %0.2f%%", cg.get_coverage());
    $finish;
  end

endmodule
