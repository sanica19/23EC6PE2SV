//------------------------------------------------------------------------------
//File       : counter.sv
//Author     : Sanica M S/1BM23EC229
//Created    : 03-02-2026
//Module     : counter
//Project    : SystemVerilog and Verification (23EC6PE2SV),
//Faculty    : Prof. Ajaykumar Devarapalli
//Description: 4-bit Synchronous Counter used for basic functional coverage example.
//------------------------------------------------------------------------------

module counter(
	input clk, rst,
  output logic [3:0] count
);
  always_ff @(posedge clk) begin
    if(rst)
      count <= 0;
    else
      count <= count + 1;
  end
endmodule
