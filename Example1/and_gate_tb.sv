// Code your testbench here
// or browse Examples
//------------------------------------------------------------------------------
//File       : and_gate_tb.sv
//Author     : Sanica M S/1BM23EC229
//Created    : 03-02-2026
//Module     : tb
//Project    : SystemVerilog and Verification (23EC6PE2SV),
//Faculty    : Prof. Ajaykumar Devarapalli
//Description: 2-input AND gate used for basic functional coverage example.
//------------------------------------------------------------------------------

`timescale 1ns/1ps

module tb;
  logic a, b, y;
  and_gate dut(.*);
  
  covergroup cg_and;
    cp_a: coverpoint a;
    cp_b: coverpoint b;
    cross_ab: cross cp_a, cp_b;
  endgroup
  
  // Declare the handle here.
  cg_and cg; 
  
  initial begin
    // 1. Create the VCD file
    $dumpfile("dump.vcd");
    
    // 2. Dump all variables in the design
    $dumpvars;

    // 3. Instantiate the covergroup
    cg = new();
  
    repeat(20) begin
      a = $urandom();
      b = $urandom();
      #5;
      cg.sample();
    end
    
    $display ("Final Coverage = %0.2f %%", cg.get_inst_coverage());
  end
endmodule
