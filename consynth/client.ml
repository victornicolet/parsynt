let port_no = 9877
let server_name = "localhost"

let main_client client_fun  =
  if Array.length Sys.argv < 3 
  then Printf.printf "usage :  client server port\n"
  else let server = Sys.argv.(1) in
       let server_addr =
         try  Unix.inet_addr_of_string server 
         with Failure("inet_addr_of_string") -> 
           try  (Unix.gethostbyname server).Unix.h_addr_list.(0) 
           with Not_found ->
             Printf.eprintf "%s : Unknown server\n" server ;
             exit 2
       in try 
            let port = int_of_string (Sys.argv.(2)) in
            let sockaddr = Unix.ADDR_INET(server_addr,port) in 
            while true do
              let ic,oc = Unix.open_connection sockaddr
              in
              client_fun ic oc ;
              Unix.shutdown_connection ic
            done
         with Failure("int_of_string") -> Printf.eprintf "bad port number";
           exit 2 ;;

let client_fun ic oc = 
  try
    print_string  "Request : " ;
    flush stdout ;
    let inp = input_line stdin in
    if inp = "END" then ( Unix.shutdown_connection ic ; raise Exit);
    output_string oc (inp^"\n") ;
    flush oc ;
    let r = input_line ic 
    in Printf.printf "Response : %s\n\n" r;
    if r = "END" then ( Unix.shutdown_connection ic ; raise Exit) ;
  with
  | Exit -> exit 0
  | exn -> Unix.shutdown_connection ic ; raise exn 

let go_client () = main_client client_fun ;;

go_client ()
