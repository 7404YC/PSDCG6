
typedef enum {ENTIRE, BIT} mon_type;
class spi_tran extends uvm_sequence_item;
    // transaction input 
    logic       rst_n;
    rand    logic       start;
    rand    logic [7:0] tx_data;

    // transaction output 
    logic       miso;
    logic [7:0] rx_data;
    logic       busy;
    logic       done;
    logic       mosi;
    logic       cs_n;


    int seq_count;
    int seq_index;
	string seq_type;
	int b2b_interval_delay;

    int tran_count;
    int tran_index;
    int tran_ready;
    string tran_type;
    string tran_dir;

    real tran_time_start;
    real tran_time_end;

    mon_type mt;
    int tran_id; 
    logic [7:0] MS_data;

    `uvm_object_utils(spi_tran)

    function new(string name = "spi_tran");
        super.new(name);
    endfunction
endclass

