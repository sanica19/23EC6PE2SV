//------------------------------------------------------------------------------
//File       : alu.sv
//Author     : Sanica M S/1BM23EC229
//Created    : 03-02-2026
//Module     : alu
//Project    : SystemVerilog and Verification (23EC6PE2SV),
//Faculty    : Prof. Ajaykumar Devarapalli
//Description: 2-input 8-bit ALU used for basic functional coverage example.
//------------------------------------------------------------------------------

package defs_pkg;
  typedef enum bit [1:0] {ADD, SUB, AND, OR} opcode_e;
endpackage

import defs_pkg::*;

module alu(
  input logic [7:0] a, b,
  input opcode_e op,
  output logic [7:0] y
);
  always_comb
    case(op)
      ADD: y = a + b;
      SUB: y = a - b;
      AND: y = a & b;
      OR:  y = a | b;
    endcase
endmodule
