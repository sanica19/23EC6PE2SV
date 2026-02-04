//------------------------------------------------------------------------------
//File       : alu.sv
//Author     : Sanica M S/1BM23EC229
//Created    : 04-02-2026
//Module     : alu
//Project    : SystemVerilog and Verification (23EC6PE2SV),
//Faculty    : Prof. Ajaykumar Devarapalli
//Description: 2-input 8-bit ALU used for basic functional coverage example.
//------------------------------------------------------------------------------

package alu_pkg;

  typedef enum bit [1:0] {
    ADD = 0,
    SUB = 1,
    MUL = 2,
    XOR = 3
  } opcode_e;

endpackage

import alu_pkg::*;

module alu (
  input  logic [7:0]  a, b,
  input  opcode_e     op,
  output logic [15:0] result
);

  always_comb begin
    case (op)
      ADD: result = a + b;
      SUB: result = a - b;
      MUL: result = a * b;
      XOR: result = a ^ b;
      default: result = '0;
    endcase
  end

endmodule

import alu_pkg::*;

class alu_transaction;

  rand logic [7:0] a, b;
  rand opcode_e   op;

  // Ensure MUL happens at least 20% of the time
  constraint op_dist {
    op dist {
      MUL := 20,
      ADD := 27,
      SUB := 27,
      XOR := 26
    };
  }

endclass
