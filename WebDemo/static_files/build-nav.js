window.addEventListener("load",buildNav);


function buildNav() {
    var navElements = getNavElements()
    wrapUpContent()
    addNavBarOpener()
    populateNavBar(navElements)
    selectCurrentNavItem()
    expandSubMenuOfCurrentNavItem()
    selectCurrentSubNavItem()
    activateMenuButton()
}

/*-------------------------------------------------------*/
/*  Get and quickly remove nav elements      */
/*-------------------------------------------------------*/

function getNavElements() {
    // get page names
    var navElements =  document.querySelectorAll('nav.top a');
     
    // Clear default nav
    $("header").html("")

    return navElements
}
/*-------------------------------------------------------*/
/*  Wrap up the existing content in a #content tag       */
/*-------------------------------------------------------*/
function wrapUpContent() {
    $("body").wrapInner('<div id="content"></div>');
}

/*-------------------------------------------------------*/
/*  Add nav bar opener      */
/*-------------------------------------------------------*/
function addNavBarOpener() {
    var navBarCode = `
        <!-- Navbar -->
         <div id="navbarcontainer">
            <div id="navbar">
               <div id="notscrollable">
                  <div class="title">
                     <a href="/#">
                     Automatically Generalizing Proofs<br/>
                     in Lean 4
                     </a>
                  </div>
                   <div class="author">
                     by <a href="http://anshula.com" target="_blank">Anshula</a> & <a href="http://github.com/0art0" target="_blank">Anand</a> & <a href="https://www.dpmms.cam.ac.uk/person/wtg10" target="_blank">Tim</a>
                  </div>
               </div>

               <div id="scrollable">
                  <div>
                     <div class="chapter" id="chapnav">
                        <span href="#" class="chaptitle">Live Demos</span>
                     </div>
                  </div>
               </div>

            </div>
         </div>
         <!-- /Navbar -->
    `

    $("body").prepend(navBarCode)
    

}




/*-------------------------------------------------------*/
/* For dynamically building the navbar based on content */
/*-------------------------------------------------------*/

function populateNavBar(navElements) {

    // Create and populate the sidebar with links to those elements
    var sidebar = document.getElementById('chapnav');
    var sidebarContent = '';
    navElements.forEach(function (element, index) {
        // Assign an id to each h2 element if it doesn't have one
        // if (element.href) {
        //     element.id = 'section' + (index + 1);
        // }

        sidebarContent += '<a href="' + element.href + '"><div class="subchaptitle">' + element.textContent + '</div></a>';
    });

    // navElements.forEach(function (element, index) {
    //     if (element.classList.contains('subchap')) {
    //         // Get all <h2> elements within this subchapter
    //         var h2Elements = element.querySelectorAll('h2');
    //         h2Elements.forEach(function (h2, idx) {
    //             // Ensure each h2 has an id for linking
    //             if (!h2.id) {
    //                 h2.id = 'subchap' + index + '-h2-' + idx;
    //             }
    //             // Append each h2 to the sidebar content
    //             sidebarContent += '<a href="#' + h2.id + '"><div class="subchaptitle">' + h2.textContent + '</div></a>';
    //         });
    //     }
    // });

    sidebarContent += '';
    sidebar.innerHTML += sidebarContent;
}

function getCurrentPage() {
    // the current blog entry page
    return window.location.href.split("#")[0].slice(0, -1); // get rid of everything after "#", then get rid of "/" at end

}

function getCurrentSubPage() {
    // the the subheading in the page (what comes after the "#" in the URL)
    return window.location.href.split("#")[1]; // get everything after "#"
}

function selectCurrentNavItem() {
        var currentLocation = getCurrentPage()
        document.querySelectorAll('#chapnav a').forEach(function(link) {
            if (link.href === currentLocation) {
                link.classList.add('selected');
            }
        });
}



function expandSubMenuOfCurrentNavItem() {
    // Get all h2 elements on the current page
    const h2Elements = document.querySelectorAll('h2');

    // Find the currently selected navbar item
    const selectedNavItem = document.querySelector('#chapnav a.selected');
    if (selectedNavItem) {
        // Create a container div under the selected nav item to hold the h2 links
        const subMenu = document.createElement('div');
        subMenu.className = 'sub-menu';
        // Generate links for each h2 and append to the sub-menu
        h2Elements.forEach(h2 => {
            if (!h2.id) {
                h2.id = `${h2.textContent.toLowerCase().replace(/\s+/g, '-')}`;
            }
            const link = document.createElement('a');
            link.href = `#${h2.id}`;
            link.textContent = h2.textContent;
            link.className = 'sub-menu-item';
            subMenu.appendChild(link);
        });
        // Append the sub-menu to the selected nav item
        selectedNavItem.appendChild(subMenu);


    // Whenever the hash link changes, re-select the current subnav item
    window.addEventListener('hashchange', function () {
        selectCurrentSubNavItem()
    });

    }


}

function selectCurrentSubNavItem() {
    var currentLocation = getCurrentSubPage()
    document.querySelectorAll('.sub-menu-item').forEach(function(link) {
        if (link.href.split("#")[1] === currentLocation) {
            link.classList.add('subselected');
        }
        else {
            link.classList.remove('subselected');
        }
    });
}
/*-------------------------------------------------------*/
/* Make navbar collapse button work */
/*-------------------------------------------------------*/

function activateMenuButton() {

    var navbarCollapseButton = `
    <button class="change navbarcollapsebutton">
        <div class="menuicon">
            <div class="bar1"></div>
            <div class="bar2"></div>
            <div class="bar3"></div>
        </div>
    </button>    
    `

    $("#content").prepend(navbarCollapseButton)


    $(".navbarcollapsebutton").click(function(){ 

        $(this).toggleClass("change"); // change the animation of the navbar collapse button
        $("#navbarcontainer").toggleClass("collapsed"); // hide the navbar
        $("#content").toggleClass("full"); // remove left margin from content (to make image wide)

        // set the current sticking comic headers to change size
        if($("#content").hasClass("full")) {
            var new_width = $("#container").outerWidth();
        }
        else {
            var new_width = $("#container").outerWidth() - $("#navbarcontainer").outerWidth();
        }
        $(".is_stuck").animate({
            width: new_width
        }, duration=200) /* just a little bit faster than duration of #navbarcontainer in css file */

   
    });
}

function updateNavbarSelection() {
    // Get all h2 headers in the content
    const headers = document.querySelectorAll('#content h2');
    
    // Get the current scroll position and viewport height
    const scrollPosition = window.scrollY;
    const viewportHeight = window.innerHeight;
    
    // Find the h2 that's at the top of the viewport
    let currentHeader = null;
    headers.forEach(header => {
        const headerTop = header.offsetTop;
        
        // Check if header is at the top of the viewport or above
        if (headerTop < scrollPosition) {
            currentHeader = header;
        }
    });
    
    // Remove all selected classes first
    document.querySelectorAll('.sub-menu-item').forEach(item => {
        item.classList.remove('subselected');
    });
    
    // Update navbar selection only if we found a header
    if (currentHeader) {
        // Find and select the corresponding navbar item
        const headerId = currentHeader.id;
        const navItem = document.querySelector(`.sub-menu-item[href="#${headerId}"]`);
        if (navItem) {
            navItem.classList.add('subselected');
        }
    }
}

// Add scroll event listener to update navbar selection
window.addEventListener('scroll', updateNavbarSelection);

// Initial call to set selection on page load
document.addEventListener('DOMContentLoaded', updateNavbarSelection);
