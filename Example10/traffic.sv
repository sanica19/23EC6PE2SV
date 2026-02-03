//------------------------------------------------------------------------------
//File       : traffic.sv
//Author     : Sanica M S/1BM23EC229
//Created    : 03-02-2026
//Module     : traffic
//Project    : SystemVerilog and Verification (23EC6PE2SV),
//Faculty    : Prof. Ajaykumar Devarapalli
//Description: Traffic Light Controller used for basic functional coverage example.
//------------------------------------------------------------------------------

package traffic_pkg;
  typedef enum bit [1:0] {RED, GREEN, YELLOW} light_t;
endpackage

import traffic_pkg::*;

module traffic(
  input logic clk, rst,
  output light_t colour
);
  
  always_ff @(posedge clk) begin
    if(rst)
      colour <= RED;
    else
      case(colour)
        RED:    colour <= GREEN;
        GREEN:  colour <= YELLOW;
        YELLOW: colour <= RED;
        default: colour <= RED;
      endcase
  end
endmodule
