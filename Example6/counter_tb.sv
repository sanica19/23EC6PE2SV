//------------------------------------------------------------------------------
//File       : counter_tb.sv
//Author     : Sanica M S/1BM23EC229
//Created    : 03-02-2026
//Module     : tb
//Project    : SystemVerilog and Verification (23EC6PE2SV),
//Faculty    : Prof. Ajaykumar Devarapalli
//Description: 4-bit Synchronous Counter used for basic functional coverage example.
//------------------------------------------------------------------------------

`timescale 1ns/1ps

module tb;
  logic clk = 0, rst;
  logic [3:0] count;
  counter dut(.*);
  always #5 clk = ~clk;
  
  covergroup cg_count @(posedge clk);
    cp_val: coverpoint count {
      bins zero = {0};
      bins max = {15};
      bins roll = (15 => 0);
    }
  endgroup

  //Declare handle here.
  cg_count cg; 
  
  initial begin
    $dumpfile("dump.vcd");
    $dumpvars;
    
    cg = new();
    
    rst = 1; 
    #20; 
    rst = 0;
    
    repeat(40) @(posedge clk);
    
    $display("Coverpoint Coverage: %0.2f %%", cg.cp_val.get_coverage());
    $finish;
  end
endmodule
