#! /bin/bash
# A small script intended to start an Apache server that serves the TACO 
# documentation

echo "Starting documentation server"
httpd -k start &> /dev/null
echo "Documentation should now be accessible under 

http://localhost:3000 


or http://localhost:<PORT> where port is the first port that was specified in \
'--publish' / '-p' when starting the container."
